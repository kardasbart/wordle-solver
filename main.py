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
    def __init__(self):
        self.screen = curses.initscr()
        self.screen.keypad(True) # Enable keypad mode for arrow keys etc.
        curses.curs_set(0)
        self.scr_height, self.scr_width = self.screen.getmaxyx()
        self.windows = dict()
        self.funcs = "ciestnrq"

        self.greeting_window_height = 2
        self.tabs_window_height = 2
        self.status_window_height = 5
        self.input_window_height = 2 # Assuming 2 lines for the input window

        self.list_display_area_start_y = (
            self.greeting_window_height
            + self.tabs_window_height
            + self.status_window_height
        )
        self.list_display_height = (
            self.scr_height
            - self.list_display_area_start_y
            - self.input_window_height
        )

        self.terminal_too_small = self.list_display_height < 3

        # UI state for list focus and scrolling
        self.active_list = "words"  # Default active list
        self.letters_scroll_offset = 0
        self.words_scroll_offset = 0

        # Initial pad dimensions and viewport coordinates
        self.initial_pad_height = 100 # Start with 100 lines, can grow
        self.letters_pad_width = 15
        self.words_pad_width = max(1, self.scr_width - 20) # Ensure at least 1

        if not self.terminal_too_small:
            self.letters_pad = curses.newpad(self.initial_pad_height, self.letters_pad_width)
            self.words_pad = curses.newpad(self.initial_pad_height, self.words_pad_width)
        else:
            # Create dummy pads if terminal is too small to prevent errors,
            # though they won't be properly displayed.
            self.letters_pad = curses.newpad(1,1)
            self.words_pad = curses.newpad(1,1)


        # Viewport coordinates: (pminrow, pmincol, sminrow, smincol, smaxrow, smaxcol)
        # sminrow, smincol, smaxrow, smaxcol define the screen rectangle for display
        self.letters_pad_viewport_coords = (
            self.list_display_area_start_y, 0, # sminrow, smincol
            self.list_display_area_start_y + self.list_display_height -1 , 14 # smaxrow, smaxcol
        )
        self.words_pad_viewport_coords = (
            self.list_display_area_start_y, 20, # sminrow, smincol
            self.list_display_area_start_y + self.list_display_height -1, self.scr_width -1 # smaxrow, smaxcol
        )


    def get_window(self, name):
        # Pads are handled separately, not as part of self.windows dictionary like regular windows.
        if name in ["letters", "words"]:
            # This case should ideally not be hit if update_letters/words are called directly.
            # If it is, it means some other part of code is trying to get them as standard windows.
            logger.warning(f"Attempted to get {name} pad via get_window. This is not standard.")
            if name == "letters":
                return self.letters_pad
            elif name == "words":
                return self.words_pad
        if name not in self.windows:
            func = getattr(self, "create_"+name)
            func()
        return self.windows[name]

    def get_string(self):
        return self.screen.getstr().decode()

    def create_greeting(self):
        self.windows["greeting"] = curses.newwin(self.greeting_window_height, self.scr_width, 0, 0)

    def update_greeting(self):
        pwin = self.get_window("greeting")
        pwin.addstr(0,0, "Wordle Solver v0.0.1! Welcome!\n")
        pwin.refresh()

    def create_progress(self):
        # Progress window y position is after greeting
        self.windows["progress"] = curses.newwin(3,self.scr_width, self.greeting_window_height,0)

    def update_progress(self, current, total):
        pwin = self.get_window("progress")
        _, width = pwin.getmaxyx()
        pwin.addstr(0, 0, f"{current} / {total} | {current / total*100:.3f}%")
        progress = "#" * ((width * current) // total)
        pwin.addstr(1, 0, f"{progress}")
        pwin.refresh()
    
    def create_status(self):
        status_y_start = self.greeting_window_height + self.tabs_window_height
        self.windows["status"] = curses.newwin(self.status_window_height,self.scr_width, status_y_start,0)

    def update_status(self, hint):
        pwin = self.get_window("status")
        pwin.clear()
        if hint is not None:
            pwin.addstr(0,0,"Current hints:")
            pwin.addstr(1,0,f"word size = {hint.size}") # Line 0
            pwin.addstr(2,0,f"correct =  {word_places(hint.corrects)}") # Line 1
            pwin.addstr(3,0,f"includes = {word_places(hint.includes)}") # Line 2
            pwin.addstr(4,0,f"excludes = {word_places(hint.excludes)}") # Line 3
        pwin.refresh()

    def create_letters(self):
        # This method might be used to draw a border or can be removed.
        # For now, pads are created in __init__.
        # If borders are needed, they would be drawn on self.screen.
        pass

    def update_letters(self, stats):
        if self.terminal_too_small: return

        self.letters_pad.clear()
        lines_written = 0
        
        prefix = "> " if self.active_list == "letters" else "  "
        title = f"{prefix}Letters %:"
        self.letters_pad.addstr(lines_written, 0, title)
        lines_written += 1

        if stats is not None:
            for k, v in stats:
                if lines_written >= self.letters_pad.getmaxyx()[0]:
                    self.letters_pad.resize(lines_written + 20, self.letters_pad_width) # Grow pad
                try:
                    self.letters_pad.addstr(lines_written, 0, f"{k}: {v:.4f}%")
                    lines_written += 1
                except curses.error: # Avoid crashing if content still doesn't fit after resize (e.g. single line too wide)
                    logger.error("Error writing to letters_pad, possibly too wide for pad width")
                    break


        pad_height, _ = self.letters_pad.getmaxyx()
        max_scroll = max(0, lines_written - self.list_display_height)
        self.letters_scroll_offset = max(0, min(self.letters_scroll_offset, max_scroll))

        # Refresh: pad_scroll_y, pad_scroll_x, sminrow, smincol, smaxrow, smaxcol
        self.letters_pad.refresh(self.letters_scroll_offset, 0, 
                                 self.letters_pad_viewport_coords[0], self.letters_pad_viewport_coords[1],
                                 self.letters_pad_viewport_coords[2], self.letters_pad_viewport_coords[3])

    def create_words(self):
        # This method might be used to draw a border or can be removed.
        # For now, pads are created in __init__.
        pass

    def update_words(self, bestwords): # idx_next removed
        if self.terminal_too_small: return

        self.words_pad.clear()
        lines_written = 0

        prefix = "> " if self.active_list == "words" else "  "
        
        if bestwords is not None:
            title = f"{prefix}Best of {len(bestwords)} words: {'score':>10} {'freq':>9}"
            self.words_pad.addstr(lines_written, 0, title)
            lines_written +=1
            
            # Iterate through words to display based on scroll offset
            # The content for the pad is all words, scrolling handles the view.
            for k, w_tuple in enumerate(bestwords): # bestwords itself is already sorted and contains all words
                if lines_written >= self.words_pad.getmaxyx()[0]:
                    self.words_pad.resize(lines_written + 50, self.words_pad_width) # Grow pad
                try:
                    # Display index is k + 1, actual word data is w_tuple
                    self.words_pad.addstr(lines_written, 0, f'{k+1:2}: {w_tuple[0]:20} {w_tuple[1]: 6.2f} {w_tuple[2]: .2E}')
                    lines_written += 1
                except curses.error:
                    logger.error("Error writing to words_pad, possibly too wide for pad width")
                    break
        else:
            self.words_pad.addstr(lines_written, 0, f"{prefix}No words to display.")
            lines_written += 1

        pad_height, _ = self.words_pad.getmaxyx()
        # self.list_display_height is the height of the viewport
        max_scroll = max(0, lines_written - self.list_display_height) 
        self.words_scroll_offset = max(0, min(self.words_scroll_offset, max_scroll))
        
        self.words_pad.refresh(self.words_scroll_offset, 0,
                               self.words_pad_viewport_coords[0], self.words_pad_viewport_coords[1],
                               self.words_pad_viewport_coords[2], self.words_pad_viewport_coords[3])

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
        win.addstr("\n")

    def create_input(self):
        input_y_start = self.scr_height - self.input_window_height
        self.windows["input"] = curses.newwin(self.input_window_height, self.scr_width, input_y_start, 0)

    def update_input(self, func):
        pwin = self.get_window("input")
        options = ["[c]orrect","[i]nclude","[e]xclude","[s]ize","[t]ab","[n]ext","so[r]t","[q]uit"]
        pwin.clear()
        self.add_list(pwin, func, dict(zip(self.funcs,options)))
        pwin.refresh()

    def create_tabs(self):
        # Tabs window y position is after greeting
        self.windows["tabs"] = curses.newwin(self.tabs_window_height, self.scr_width, self.greeting_window_height, 0)

    def update_tabs(self, current, all_tabs):
        pwin = self.get_window("tabs")
        pwin.clear()
        pwin.addstr("TABS: ")
        self.add_list(pwin, current, all_tabs)
        pwin.refresh()

    def clear(self):
        self.screen.clear()
        self.screen.refresh()

    def update_main(self,currnet_tab, all_tabs, hint, stats, bestwords): # idx_next removed
        if self.terminal_too_small:
            # Clear screen before attempting to write error message
            self.screen.clear()
            msg = "Terminal too small. Please resize."
            # Check if screen is large enough for the message itself
            if self.scr_height > 0 and self.scr_width > len(msg):
                self.screen.addstr(self.scr_height // 2, (self.scr_width - len(msg)) // 2, msg)
            else:
                # If not, try a very minimal message at 0,0 if possible
                try:
                    self.screen.addstr(0,0, "Too small")
                except curses.error:
                    pass # Can't do anything if screen is impossibly small
            self.screen.refresh()
            return

        # Before drawing main UI, ensure screen is clear, especially if resizing from too_small state
        self.screen.clear() 

        self.update_greeting()
        self.update_tabs(currnet_tab, all_tabs)
        self.update_status(hint)
        self.update_letters(stats)
        self.update_words(bestwords) # idx_next removed
        # Input line is updated in the main loop based on active_command

    def update_loading(self, current, total):
        # Check for terminal size even during loading, as greeting is shown
        if self.terminal_too_small:
            self.screen.clear()
            msg = "Terminal too small for loading screen."
            # Try to display message, might fail if terminal is extremely small
            try:
                if self.scr_height > 0 and self.scr_width > len(msg):
                    self.screen.addstr(self.scr_height // 2, (self.scr_width - len(msg)) // 2, msg)
                else:
                    self.screen.addstr(0,0,"Too small")
            except curses.error:
                pass # Can't do much if it's this small
            self.screen.refresh()
            # Potentially wait and exit or raise specific error here if loading can't proceed
            return

        self.screen.clear() # Clear before drawing loading screen
        self.update_greeting()
        self.update_progress(current, total)

    def get_args(self):
        pwin = self.get_window("input")
        curses.echo() # Enable echo for getstr
        args = pwin.getstr().decode().lower()
        curses.noecho() # Disable echo after getstr
        pwin.clear()
        pwin.refresh()
        return args

def main():
    ui = UserInterface()
    curses.noecho() # Set noecho globally for the application

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
    # idx_next is now replaced by ui.words_scroll_offset for display
    sorting_strategy = 2
    
    active_command = None

    while True:
        current_hint = tabs[current_tab]
        # Potentially, apply_filter and calc_stats could be skipped if no relevant data changed
        result = worddict.apply_filter(current_hint)
        stats, bestwords = calc_stats(result, freq, sorting_strategy)
        
        # Pass ui.words_scroll_offset instead of idx_next -> now no scroll offset passed
        ui.update_main(current_tab, tabs.keys(), current_hint, stats, bestwords)
        ui.update_input(active_command) # Show current active command or None

        # Make getch non-blocking; timeout can be adjusted or set once outside loop if preferred
        # For responsive UI update on resize, or other external events, timeout is good in loop.
        ui.screen.timeout(100) 
        key = ui.screen.getch()

        if key == curses.KEY_LEFT or key == curses.KEY_RIGHT:
            if ui.active_list == "words":
                ui.active_list = "letters"
            else:
                ui.active_list = "words"
            active_command = None # Clear any pending command
        elif key == curses.KEY_UP:
            if ui.active_list == "letters":
                ui.letters_scroll_offset = max(0, ui.letters_scroll_offset - 1)
            elif ui.active_list == "words":
                ui.words_scroll_offset = max(0, ui.words_scroll_offset - 1)
            active_command = None
        elif key == curses.KEY_DOWN:
            if ui.active_list == "letters":
                # Max limit is handled by update_letters before refresh
                ui.letters_scroll_offset += 1 
            elif ui.active_list == "words":
                # Max limit is handled by update_words before refresh
                ui.words_scroll_offset += 1 
            active_command = None
        elif key != -1 and key < 256 and chr(key) in ui.funcs: # Check key < 256 for printable chars
            func_char = chr(key).lower()
            active_command = func_char # Store the command character

            if func_char == 'q':
                break

            ui.update_input(active_command) # Update UI to show current command
            args = ui.get_args()
            active_command = None # Clear active command after getting args
            # ui.update_input(None) # Already handled by next loop's update_input(active_command)

            try:
                if func_char == "s":
                    size = int(args)
                    tabs[current_tab] = HintConfig(size)
                    # Reset scrolls and active list for new size
                    ui.words_scroll_offset = 0
                    ui.letters_scroll_offset = 0
                    ui.active_list = "words" 
                elif func_char == "c":
                    if "#" in args:
                        current_hint.clear_corrects()
                    else:
                        for k_arg, v_arg in split_args(current_hint.size, args).items():
                            current_hint.correct(k_arg, v_arg)
                elif func_char == "i":
                    if "#" in args:
                        logger.info(args)
                        current_hint.clear_includes()
                    else:
                        for k_arg, v_arg in split_args(current_hint.size, args).items():
                            current_hint.include(k_arg, v_arg)
                elif func_char == "e":
                    args = args.replace(" ", "")
                    if "#" in args:
                        current_hint.clear_excludes()
                    else:
                        for l_arg in set(args):
                            current_hint.exclude(l_arg)
                elif func_char == "n": # Go to word number (1-indexed)
                    if args != "":
                        try:
                            target_item_number = int(args)
                            # Convert 1-indexed user input to 0-indexed scroll offset
                            ui.words_scroll_offset = max(0, target_item_number - 1) 
                        except ValueError:
                            logger.warn(f"Invalid argument for 'n' command (expected a number): {args}")
                            pass # Or display an error to the user
                    else:
                        ui.words_scroll_offset = 0 # Go to top (item 1)
                elif func_char == "r": # Sort strategy
                    if args in ["0","1","2"]:
                        sorting_strategy = int(args)          
                elif func_char == "t": # Tab management
                    if args in tabs:
                        current_tab = args
                    else:
                        tabs.update({args: copy.copy(current_hint)})
                        current_tab = args
            except Exception as e:
                logger.error(f"Error processing command {func_char} with args {args}: {e} {traceback.format_exc()}")
                # Optionally, display an error message in the UI status bar
                pass # Continue running
        elif key != -1 and key < 256 and chr(key) == 'q': # Explicitly check for 'q' if not in ui.funcs
             break
        elif key == curses.KEY_RESIZE: # Handle terminal resize
            ui.scr_height, ui.scr_width = ui.screen.getmaxyx()
            ui.list_display_area_start_y = (
                ui.greeting_window_height + ui.tabs_window_height + ui.status_window_height
            )
            ui.list_display_height = (
                ui.scr_height - ui.list_display_area_start_y - ui.input_window_height
            )
            ui.terminal_too_small = ui.list_display_height < 3

            # Update pad viewport coordinates and potentially recreate/resize windows
            if not ui.terminal_too_small:
                # Update fixed window dimensions by recreating them
                # Their create methods use self.scr_width and self.scr_height implicitly or via calculated positions
                ui.create_greeting() 
                ui.create_tabs()
                ui.create_status()
                ui.create_input()

                # Update letters pad viewport (width is fixed)
                ui.letters_pad_viewport_coords = (
                    ui.list_display_area_start_y, 0, # sminrow, smincol
                    ui.list_display_area_start_y + ui.list_display_height - 1, ui.letters_pad_width -1 # smaxrow, smaxcol
                )

                # Update words pad width and resize it, then update viewport
                ui.words_pad_width = max(1, ui.scr_width - 20)
                try:
                    current_words_pad_rows, _ = ui.words_pad.getmaxyx()
                    ui.words_pad.resize(current_words_pad_rows, ui.words_pad_width)
                except curses.error as e:
                    logger.error(f"Error resizing words_pad: {e}")
                    # Fallback: recreate if resize fails (e.g. new width too small for content)
                    # This might lose content if not handled carefully, but pads are repopulated anyway
                    ui.words_pad = curses.newpad(ui.initial_pad_height, ui.words_pad_width)


                ui.words_pad_viewport_coords = (
                    ui.list_display_area_start_y, 20, # sminrow, smincol
                    ui.list_display_area_start_y + ui.list_display_height - 1, ui.scr_width -1 # smaxcol for viewport
                )
            
            # Scroll offsets will be clamped by update_letters/update_words in the next full refresh
            # which is triggered by the loop continuing.

            ui.screen.clear() # Clear physical screen fully to prevent artifacts
            # Loop will redraw everything in the next iteration.
            active_command = None


        elif key == -1: # Timeout
            pass # Just continue, UI will be updated

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