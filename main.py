import sys
import pickle
import os
import copy
import time
import itertools
import json
from itertools import chain, combinations
import functools
import curses
import logging
import re
import signal
import sys
import traceback
from sortedcontainers import SortedList, SortedDict, SortedSet


logger = logging.getLogger(__file__)
hdlr = logging.FileHandler(__file__ + ".log")
formatter = logging.Formatter("%(asctime)s %(levelname)s %(message)s")
hdlr.setFormatter(formatter)
logger.addHandler(hdlr)
logger.setLevel(logging.DEBUG)


class WordLenException(Exception):
    pass


class WordStorage:
    def __init__(self):
        self.data = dict()
        self.cnt = 0

    def push(self, word):
        idx = self.cnt
        self.cnt += 1
        self.data[idx] = word
        return idx

    def get(self, idx):
        return self.data[idx]


class WordDict:
    def __init__(self):
        self.storage = WordStorage()
        self.words_by_size = dict()
        self.letter_sets = dict()
        self.letter_lookup = dict()

    def push(self, word):
        size = len(word)
        idx = self.storage.push(word)

        if size not in self.words_by_size:
            self.words_by_size[size] = SortedSet()
        self.words_by_size[size].add(idx)

        for k in range(size):
            letter = word[k]
            key = (size, letter, k)
            if key not in self.letter_sets:
                self.letter_sets[key] = SortedSet()
            if (size, letter) not in self.letter_lookup:
                self.letter_lookup[(size, letter)] = SortedSet()
            self.letter_sets[key].add(idx)
            self.letter_lookup[(size, letter)].add(idx)

    def filter(self, init_set, key, func):
        bound_func = functools.partial(func, init_set)
        if key not in self.letter_sets:
            return init_set
        filtered = self.letter_sets[key]
        return bound_func(filtered)

    def apply_filter(self, config):
        if config.size not in self.words_by_size:
            init_set = SortedSet(self.storage.data.keys())
        else:
            init_set = self.words_by_size[config.size]
        
            for mode, key, func in config.rules():
                logger.info(f"{mode}, {key}, {func}")
                if mode == "simple":
                    init_set = self.filter(init_set, key, func)
                elif mode == "include":
                    filtered = self.letter_lookup[(config.size, key)]
                    init_set = init_set.intersection(filtered)

        ret = [self.storage.get(idx) for idx in init_set]
        return ret


class HintConfig:
    def __init__(self, size):
        self.corrects = dict()
        self.includes = dict()
        self.excludes = set()
        self.size = size

    def clear_excludes(self):
        self.excludes = set()

    def clear_includes(self):
        self.includes = dict()

    def clear_corrects(self):
        self.corrects = dict()

    def exclude(self, letter):
        if letter in self.excludes:
            self.excludes.remove(letter)
        else:
            self.excludes.add(letter)

    def handle_letter_positions(self, container, letter, positions):
        if letter in container:
            old = container[letter]
        else:
            old = set()
        if -1 in positions or len(positions) == 0:
            if letter in container:
                del container[letter]
        else:
            container.update({letter: set([*positions, *list(old)])})

    def include(self, letter, positions):
        self.handle_letter_positions(self.includes, letter, positions)

    def correct(self, letter, positions):
        self.handle_letter_positions(self.corrects, letter, positions)

    def rules(self):
        rules = []
        for letter, positions in self.corrects.items():
            for p in positions:
                key = (self.size, letter, p)
                func = SortedSet.intersection
                rules.append(("simple", key, func))

        for letter in self.includes.keys():
            rules.append(("include", letter, None))

        pos_left = set(range(self.size)) - set(
            [x for xs in self.corrects.values() for x in xs]
        )

        for letter, position in itertools.product(self.excludes, pos_left):
            key = (self.size, letter, position)
            func = SortedSet.difference
            rules.append(("simple", key, func))

        for letter, positions in self.includes.items():
            pos_left = set(range(self.size)) - set(positions)
            for position in positions:
                key = (self.size, letter, position)
                func = SortedSet.difference
                rules.append(("simple", key, func))

        return rules


def calc_stats(result, freq, strategy):
    letters = dict()
    cnt = 0
    for word in result:
        for l in word:
            cnt += 1
            if l in letters:
                letters[l] += 1
            else:
                letters[l] = 1
    rank = sorted([(k, v / cnt * 100) for k, v in letters.items()], key=lambda x: -x[1])
    rank_dict = {a[0]: a[1] for a in rank}
    bestlist = SortedSet(key=lambda x: -x[strategy] if strategy > 0 else x[strategy])

    for w in result:
        ws = sorted(set(w))
        score = 0
        for l in ws:
            score += rank_dict[l]
        if w in freq:
            bestlist.add((w, score, freq[w]))
        else:
            bestlist.add((w, score, 0))

    return rank, bestlist

def split_iterable(value):
    result = dict()
    current_letter = None
    for c in value:
        if str(c).isnumeric():
            if c == "0":
                c = 10
            result[current_letter].add(int(c) - 1)
        elif str(c) == "#":
            result[current_letter].add(-1)
        else:
            current_letter = c
            if c not in result:
                result[c] = set()
    return result


def split_args(size, value):
    if size >= 11:
        value = value.split()
    else:
        value = value.replace(" ", "")
    return split_iterable(value)

def word_places(iterable):
    input_dict = dict()
    if isinstance(iterable,set):
        input_dict = { x : set() for x in iterable }
    else:
        input_dict = iterable.copy()
    if len(input_dict):
        result = "{ " 
        for k, v in input_dict.items():
            result += k
            if len(v) != 0:
                result += ": " + str(sorted(list([x+1 for x in v])))
            result += ", "
        result= result[:-2] + " }"
    else:
        result = "{}"
    return result
    

class UserInterface:
    MIN_TERMINAL_HEIGHT = 53
    MIN_TERMINAL_WIDTH = 62

    def __init__(self):
        self.screen = curses.initscr()
        curses.curs_set(0)
        self.scr_height, self.scr_width = self.screen.getmaxyx()
        self.windows = dict()
        self.funcs = "ciestnrq"

    def check_terminal_size_and_display_message(self):
        h, w = self.screen.getmaxyx()
        if h < UserInterface.MIN_TERMINAL_HEIGHT or w < UserInterface.MIN_TERMINAL_WIDTH:
            self.screen.clear()
            msg = "Sorry this is too small window, please resize!"
            
            # Truncate message if width is too small
            # w-1 to leave space for cursor/border if window is exactly len(msg) wide
            safe_msg = msg[:max(0, w -1)] # Ensure slice index is not negative
            
            # Attempt to center the message
            msg_y = h // 2
            msg_x = (w - len(safe_msg)) // 2
            
            # Ensure coordinates are valid (non-negative and within screen bounds)
            if msg_y >= h: # If h=0, msg_y will be 0. If h=1, msg_y will be 0.
                msg_y = 0
            if msg_x < 0: # If safe_msg is empty (w=0 or 1), msg_x could be 0 or negative.
                msg_x = 0
            # Also ensure msg_x + len(safe_msg) does not exceed width
            if msg_x + len(safe_msg) > w:
                msg_x = 0 # Fallback to (0,0) if centering makes it go out of bounds

            try:
                # Ensure addstr itself doesn't try to write out of bounds if h or w is 0
                if h > 0 and w > 0 :
                    self.screen.addstr(msg_y, msg_x, safe_msg)
            except curses.error:
                # Fallback for very small screens or other addstr errors
                try:
                    self.screen.clear() # Clear again
                    # Ensure "Resize!" fits, even if w is very small
                    fallback_msg = "Resize!"[:max(0, w - 1)]
                    if h > 0 and w > 0 and len(fallback_msg) > 0:
                         self.screen.addstr(0, 0, fallback_msg)
                except curses.error:
                    pass # Give up if screen is truly unusable
            self.screen.refresh()
            return False
        return True

    def get_window(self, name):
        if name not in self.windows:
            func = getattr(self, "create_"+name)
            func()
        return self.windows[name]

    def get_string(self):
        return self.screen.getstr().decode()

    def create_greeting(self):
        self.windows["greeting"] = curses.newwin(2, self.scr_width, 0, 0)

    def update_greeting(self):
        pwin = self.get_window("greeting")
        pwin.addstr(0,0, "Wordle Solver v0.0.1! Welcome!\n")
        pwin.refresh()

    def create_progress(self):
        self.windows["progress"] = curses.newwin(3,self.scr_width, 2,0)

    def update_progress(self, current, total):
        pwin = self.get_window("progress")
        _, width = pwin.getmaxyx()
        pwin.addstr(0, 0, f"{current} / {total} | {current / total*100:.3f}%")
        progress = "#" * ((width * current) // total)
        pwin.addstr(1, 0, f"{progress}")
        pwin.refresh()
    
    def create_status(self):
        self.windows["status"] = curses.newwin(5,self.scr_width, 4,0)

    def update_status(self, hint):
        pwin = self.get_window("status")
        pwin.clear()
        if hint is not None:
            pwin.addstr(0,0,"Current hints:")
            pwin.addstr(1,0,f"word size = {hint.size}")
            pwin.addstr(2,0,f"correct =  {word_places(hint.corrects)}")
            pwin.addstr(3,0,f"includes = {word_places(hint.includes)}")
            pwin.addstr(4,0,f"excludes = {word_places(hint.excludes)}")
        pwin.refresh()

    def create_letters(self):
        # The window starts at y-offset 10.
        # Ensure there's at least 1 line for the window itself.
        available_height = max(1, self.scr_height - 10) 
        
        # Use min of original fixed height (40), available_height,
        # and ensure at least 1 line high.
        window_height = max(1, min(40, available_height))
        
        self.windows["letters"] = curses.newwin(window_height, 15, 10, 0)

    def update_letters(self, stats):
        pwin = self.get_window("letters")
        pwin.clear()
        if stats is not None:
            h, w = pwin.getmaxyx()

            if h == 0: # Should not happen due to create_letters using max(1, ...)
                pwin.refresh()
                return

            available_lines_for_items = 0
            # 1. Handle header printing with conditional newline
            if h == 1:
                pwin.addstr("Letters %:")
                # No lines available for items if header takes the only line
                available_lines_for_items = 0 
            else: # h > 1
                pwin.addstr("Letters %:\n")
                # Lines available after header (which includes a newline)
                available_lines_for_items = h - 1

            # Ensure available_lines_for_items is not negative (already handled by h checks)
            # available_lines_for_items = max(0, available_lines_for_items) # Redundant if h>=1
            
            displayed_stats = stats[:available_lines_for_items]
            
            # 2. Handle items printing with conditional newline
            # If h=1, available_lines_for_items is 0, so this loop won't run.
            # If h>1, header is on line 0, items start on line 1.
            for idx, (k, v) in enumerate(displayed_stats):
                item_str = f"{k}: {v:.4f}%"
                
                # current_item_line_idx is the 0-indexed line where this item will be printed.
                # If h > 1, header was on line 0, items start on line 1.
                # So, the first item (idx=0) goes to line 1.
                current_item_line_idx = 1 + idx 

                # Add newline if this item is NOT on the last line of the window (h-1)
                if current_item_line_idx < h - 1:
                    item_str += "\n"
                # else: item is on the last line (h-1), or something is wrong if > h-1
                
                pwin.addstr(item_str)

        pwin.refresh()

    def create_words(self):
        # y-offset is 10
        available_height = max(1, self.scr_height - 10) 
        words_window_height = max(1, min(40, available_height))

        # x-offset is 20
        # Ensure width is at least 1, and uses screen width minus offset
        words_window_width = max(1, self.scr_width - 20) 
        
        self.windows["words"] = curses.newwin(words_window_height, words_window_width, 10, 20)

    def update_words(self, bestwords, idx_next):
        pwin = self.get_window("words")
        pwin.clear()
        if bestwords is not None:
            h, w = pwin.getmaxyx()

            if h == 0: # Window unusable
                pwin.refresh()
                return

            header_str = f"Best of {len(bestwords)} words: {'score':>10} {'freq':>9}"
            available_lines_for_items = 0
            
            # Max number of characters to print per line (for addnstr)
            # Ensures that we don't try to write past the window width.
            # -1 because addnstr writes *at most* n characters. If w=0, n_to_print=0.
            n_to_print = max(0, w - 1) 

            if h == 1:
                pwin.addnstr(header_str, n_to_print)
            else: # h > 1
                # addnstr will include the \n if it fits within n_to_print characters.
                # If header_str itself is already w-1, \n won't be printed.
                pwin.addnstr(header_str + "\n", n_to_print)
                available_lines_for_items = h - 1
            
            available_lines_for_items = max(0, available_lines_for_items)
            
            start_idx = idx_next
            if start_idx < 0: start_idx = 0
            start_idx = min(start_idx, len(bestwords)) # Ensure start_idx is not out of bounds

            end_idx = min(start_idx + available_lines_for_items, len(bestwords))
            displayed_words = bestwords[start_idx:end_idx]
            
            for k_loop, word_data in enumerate(displayed_words):
                item_str = f'{start_idx + k_loop + 1:2}: {word_data[0]:20} {word_data[1]:6.2f} {word_data[2]:.2E}'
                
                # current_item_line_idx is the 0-indexed line this item will occupy,
                # assuming header (if h>1) was on line 0.
                current_item_line_idx = 1 + k_loop 

                final_item_str_with_nl = item_str # Assume no newline first
                if current_item_line_idx < h - 1: # If not the very last line of the window
                    final_item_str_with_nl += "\n"
                
                try:
                    # Add the string, truncated by n_to_print.
                    # If \n is part of the truncated string, it will be processed.
                    pwin.addnstr(final_item_str_with_nl, n_to_print)
                except curses.error:
                    logger.error(f"Error in update_words: addnstr failed for item (h:{h},w:{w},n:{n_to_print}). Item: {item_str}")
                    break 
        pwin.refresh()

    def add_list(self, win, current, all):
        if not isinstance(all, dict):
            all_dict = dict(zip(all,all))
        else:
            all_dict = all

        for idx, opt in enumerate(all_dict.items()):
            key, value = opt
            if current == key:
                win.addstr(value, curses.A_STANDOUT)
            else:
                win.addstr(value)
            if idx != len(all_dict)-1:
                win.addstr(" | ")
        
        y, x = win.getyx()
        h, w = win.getmaxyx()
        if y < h - 1: # Only add newline if not already on the last line
            win.addstr("\n")

    def create_input(self):
        self.windows["input"] = curses.newwin(3,self.scr_width, 50, 0)

    def update_input(self, func):
        pwin = self.get_window("input")
        options = ["[c]orrect","[i]nclude","[e]xclude","[s]ize","[t]ab","[n]ext","so[r]t","[q]uit"]
        pwin.clear()
        self.add_list(pwin, func, dict(zip(self.funcs,options)))
        pwin.refresh()

    def create_tabs(self):
        self.windows["tabs"] = curses.newwin(2,self.scr_width, 2, 0)

    def update_tabs(self, current, all_tabs):
        pwin = self.get_window("tabs")
        pwin.clear()
        pwin.addstr("TABS: ")
        self.add_list(pwin, current, all_tabs)
        pwin.refresh()

    def clear(self):
        self.screen.clear()
        self.screen.refresh()

    def update_main(self,currnet_tab, all_tabs, hint, stats, bestwords, idx_next):
        self.update_greeting()
        self.update_tabs(currnet_tab, all_tabs)
        self.update_status(hint)
        self.update_letters(stats)
        self.update_words(bestwords, idx_next)

    def update_loading(self, current, total):
        self.update_greeting()
        self.update_progress(current, total)

    def handle_resize(self):
        """Handles terminal resize events."""
        h, w = self.screen.getmaxyx() # Get new size first
        
        try:
            curses.resizeterm(h, w)      # Inform curses
        except Exception as e: # pragma: no cover
            logger.error(f"curses.resizeterm({h}, {w}) failed: {e}")
            # Even if resizeterm fails, we should update our internal dimensions
            # and attempt to redraw.
        
        self.scr_height, self.scr_width = h, w # Update instance variables

        self.screen.clear()
        # Crucial: Refresh after clear so check_terminal_size_and_display_message 
        # sees a clean slate for its getmaxyx if it calls it internally,
        # or so its message is on a clean screen.
        self.screen.refresh() 

        is_size_ok = self.check_terminal_size_and_display_message()

        if is_size_ok:
            # If size is okay, re-create all windows.
            self.create_greeting()
            self.create_progress() 
            self.create_status()
            self.create_letters()
            self.create_words()
            self.create_input()
            self.create_tabs()
            # Refresh the screen to show newly created windows.
            # check_terminal_size_and_display_message refreshes if it returns False (size not ok).
            # If it returned True (meaning size is OK), it doesn't refresh, so we do it here.
            self.screen.refresh()
        # If is_size_ok is False, check_terminal_size_and_display_message has already
        # cleared, displayed a message, and refreshed the screen.
        
        return is_size_ok

    def get_func(self):
        pwin = self.get_window("input")
        curses.noecho()
        while True:
            key_press = pwin.getch()  # Get the raw key press
            
            if key_press == curses.KEY_RESIZE:
                # No need to call curses.echo() here as it's not a character input
                return curses.KEY_RESIZE  # Return KEY_RESIZE directly
            
            # If not KEY_RESIZE, try to convert to char and process
            try:
                func = chr(key_press).lower()
                if func in self.funcs:
                    curses.echo()  # Call echo before returning the valid function character
                    return func
            except ValueError:
                # If chr(key_press) fails (e.g. for other special keys like F1, arrows),
                # just ignore and loop again to wait for a valid input.
                pass
            # If it was a character but not in self.funcs, the loop also continues.

    def get_args(self):
        pwin = self.get_window("input")
        args = pwin.getstr().decode().lower()
        pwin.clear()
        pwin.refresh()
        return args

def main():
    ui = UserInterface()
    last_resize_handle_time = 0
    RESIZE_DEBOUNCE_DELAY = 0.25 # 250 milliseconds

    # Initial terminal size check
    is_size_ok = ui.check_terminal_size_and_display_message()

    while not is_size_ok:
        key = ui.screen.getch() # Wait for input/event
        if key == curses.KEY_RESIZE:
            current_time = time.time()
            if current_time - last_resize_handle_time < RESIZE_DEBOUNCE_DELAY:
                continue # Skip this resize event
            last_resize_handle_time = current_time
            # handle_resize should update screen dimensions and recreate windows.
            # The subsequent call to check_terminal_size_and_display_message
            # will then use these new dimensions.
            # Note: handle_resize now calls check_terminal_size_and_display_message itself.
            is_size_ok = ui.handle_resize() 
            # is_size_ok = ui.check_terminal_size_and_display_message() # This call is now redundant
        # TODO: Optionally add other key handling here (e.g., quit key)

    # Proceed with application setup only if size is okay
    num_lines = sum(1 for _ in open(sys.argv[1]))
    worddict = WordDict()
    with open(sys.argv[1], "r") as file:
        # Read each line in the file
        for idx, line in enumerate(file):
            ui.update_loading(idx+1, num_lines)
            word = line.strip()
            worddict.push(word)
    ui.clear()

    freq = [ a.split() for a in open(sys.argv[2]) ]
    freq = {a[0] : float(a[1]) for a in freq}

    tabs = {"0": HintConfig(0)}
    current_tab = "0"
    result = None
    stats = None
    idx_next = 0
    sorting_strategy = 2
    
    should_draw_main_ui = True # Initially true as startup check passed

    while True:
        if not should_draw_main_ui:
            # Screen is too small, wait for resize or quit
            key = ui.screen.getch()
            if key == curses.KEY_RESIZE:
                current_time = time.time()
                if current_time - last_resize_handle_time < RESIZE_DEBOUNCE_DELAY:
                    continue
                last_resize_handle_time = current_time
                should_draw_main_ui = ui.handle_resize()
            elif key == ord('q'):
                break
            continue

        # If should_draw_main_ui is True:
        current_hint = tabs[current_tab]
        result = worddict.apply_filter(current_hint)
        stats, bestwords = calc_stats(result, freq, sorting_strategy)
        ui.update_main(current_tab, tabs.keys(), current_hint, stats, bestwords, idx_next)

        ui.update_input(None)
        
        # Get the function or special key (like KEY_RESIZE) from get_func
        func_or_key_pressed = ui.get_func()

        if func_or_key_pressed == curses.KEY_RESIZE:
            current_time = time.time()
            if current_time - last_resize_handle_time < RESIZE_DEBOUNCE_DELAY:
                continue
            last_resize_handle_time = current_time
            should_draw_main_ui = ui.handle_resize()  # Call handle_resize if KEY_RESIZE was returned
        else:
            # If it wasn't KEY_RESIZE, it must be a normal function character
            func = func_or_key_pressed  # Assign to func to keep existing logic flow
            
            ui.update_input(func) # Show the selected function
            if func == "q":
                break
            args = ui.get_args() # Get arguments for the function
            try:
                if func == "s":
                    size = int(args)
                    tabs[current_tab] = HintConfig(size)
                elif func == "c":
                    if "#" in args:
                        current_hint.clear_corrects()
                    else:
                        for k, v in split_args(current_hint.size, args).items():
                            current_hint.correct(k, v)
                elif func == "i":
                    if "#" in args:
                        logger.info(args)
                        current_hint.clear_includes()
                    else:
                        for k, v in split_args(current_hint.size, args).items():
                            current_hint.include(k, v)
                elif func == "e":
                    args = args.replace(" ", "")
                    if "#" in args:
                        current_hint.clear_excludes()
                    else:
                        for l in set(args):
                            current_hint.exclude(l)
                elif func == "n":
                    if args != "":
                        idx_next = int(args)
                    else:
                        idx_next = 0
                elif func == "r":
                    if args in ["0","1","2"]:
                        sorting_strategy = int(args)          
                elif func == "t":
                    if args in tabs:
                        current_tab = args
                    else:
                        tabs.update({args: copy.copy(current_hint)})
                        current_tab = args
            except:
                pass

def signal_handler(sig, frame):
    curses.endwin()
    sys.exit(0)

if __name__ == "__main__":
    signal.signal(signal.SIGINT, signal_handler)
    try:
        main()
    except Exception as e:
        curses.endwin()
        print(traceback.format_exc())
        sys.exit(-1)
    curses.endwin()