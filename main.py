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
    MIN_TERMINAL_HEIGHT = 15  # Minimum overall terminal height
    MIN_TERMINAL_WIDTH = 30   # Minimum overall terminal width
    
    # Fixed window heights
    GREETING_H = 2
    TABS_H = 2
    STATUS_H = 5
    INPUT_H = 2

    # Pad widths (letters pad is fixed, words pad relative to screen)
    LETTERS_PAD_FIXED_WIDTH = 15
    WORDS_PAD_RIGHT_MARGIN = 20 # from left edge of screen

    def __init__(self):
        self.screen = curses.initscr()
        self.screen.keypad(True)
        curses.curs_set(0)
        
        self.scr_height, self.scr_width = 0, 0 # Initialized by handle_resize
        self.windows = dict()
        self.funcs = "ciestnrq"

        # Layout attributes - will be calculated in handle_resize
        self.list_display_area_start_y = 0
        self.list_display_height = 0
        self.list_area_is_too_small = True # Assume too small until handle_resize confirms

        # UI state for list focus and scrolling
        self.active_list = "words"
        self.letters_scroll_offset = 0
        self.words_scroll_offset = 0

        # Pads - initialized to None, created in handle_resize if space permits
        self.letters_pad = None
        self.words_pad = None
        self.initial_pad_height = 100 # Default internal height for pads when created

        self.words_pad_width = 0 # Calculated in handle_resize
        self.letters_pad_viewport_coords = (0,0,0,0) # Placeholder
        self.words_pad_viewport_coords = (0,0,0,0)   # Placeholder
        
        # self.terminal_too_small is effectively replaced by checks in handle_resize 
        # and list_area_is_too_small for more nuanced handling.

    def check_terminal_size_and_display_message(self, custom_message=None):
        """
        Checks if the terminal is smaller than MIN_TERMINAL_HEIGHT/WIDTH or if a custom message is provided.
        If too small or custom message, clears screen and displays the message.
        Returns False if too small or custom message shown, True otherwise.
        """
        too_small_overall = (self.scr_height < UserInterface.MIN_TERMINAL_HEIGHT or 
                             self.scr_width < UserInterface.MIN_TERMINAL_WIDTH)

        message_to_display = None
        if custom_message:
            message_to_display = custom_message
        elif too_small_overall:
            message_to_display = "Terminal too small. Please resize."

        if message_to_display:
            self.screen.clear()
            try:
                # Center the message if possible
                msg_y = self.scr_height // 2
                msg_x = (self.scr_width - len(message_to_display)) // 2
                if msg_y >= 0 and msg_x >=0: # Ensure coordinates are not negative
                     self.screen.addstr(msg_y, msg_x, message_to_display)
                else: # Fallback for extremely small terminals
                    self.screen.addstr(0, 0, "Too small")
            except curses.error: # If even that fails
                pass 
            self.screen.refresh()
            return False
        return True

    def handle_resize(self):
        """
        Handles terminal resize events. Recalculates layout, recreates windows,
        updates pad viewports, and checks if the UI can be meaningfully drawn.
        Returns True if the main UI can be drawn, False otherwise.
        """
        h, w = self.screen.getmaxyx()
        try:
            if h != self.scr_height or w != self.scr_width: # Only if dimensions actually changed
                curses.resizeterm(h, w)
        except Exception as e:
            logger.error(f"Error in curses.resizeterm: {e}")
            # Continue, hoping for the best or that subsequent operations handle it
        
        self.scr_height, self.scr_width = h, w
        self.screen.clear() # Clear before any drawing or message
        # self.screen.refresh() # Refresh after clear, before message check

        if not self.check_terminal_size_and_display_message():
            self.list_area_is_too_small = True # Ensure this is set
            return False # Overall terminal too small

        # Recalculate dynamic layout properties
        self.list_display_area_start_y = ( UserInterface.GREETING_H 
                                         + UserInterface.TABS_H 
                                         + UserInterface.STATUS_H )
        input_window_y_start = self.scr_height - UserInterface.INPUT_H
        self.list_display_height = input_window_y_start - self.list_display_area_start_y
        
        self.list_area_is_too_small = self.list_display_height < 3

        if self.list_area_is_too_small:
            # Use the generic message for now, or a specific one for list area
            self.check_terminal_size_and_display_message("List display area too small.")
            return False # Main UI cannot be meaningfully drawn

        # If we reach here, terminal and list area are usable
        
        # Recreate/move fixed windows
        self.create_greeting() # at 0,0
        self.create_tabs()     # at self.GREETING_H, 0
        self.create_status()   # at self.GREETING_H + self.TABS_H, 0
        self.create_input()    # at input_window_y_start, 0

        # Create pads if they don't exist (e.g., first run or recovery from too_small)
        if self.letters_pad is None:
            self.letters_pad = curses.newpad(self.initial_pad_height, UserInterface.LETTERS_PAD_FIXED_WIDTH)
        
        new_words_pad_width = max(1, self.scr_width - UserInterface.WORDS_PAD_RIGHT_MARGIN)
        if self.words_pad is None:
            self.words_pad = curses.newpad(self.initial_pad_height, new_words_pad_width)
            self.words_pad_width = new_words_pad_width
        elif self.words_pad_width != new_words_pad_width:
            try:
                self.words_pad.resize(self.words_pad.getmaxyx()[0], new_words_pad_width)
                self.words_pad_width = new_words_pad_width
            except curses.error as e:
                logger.error(f"Error resizing words_pad, recreating: {e}")
                self.words_pad = curses.newpad(self.initial_pad_height, new_words_pad_width)
                self.words_pad_width = new_words_pad_width
        
        # Update pad viewport coordinates
        self.letters_pad_viewport_coords = (
            self.list_display_area_start_y, 0, # sminrow, smincol
            self.list_display_area_start_y + self.list_display_height - 1, 
            UserInterface.LETTERS_PAD_FIXED_WIDTH - 1 # smaxcol
        )
        self.words_pad_viewport_coords = (
            self.list_display_area_start_y, UserInterface.WORDS_PAD_RIGHT_MARGIN, # sminrow, smincol
            self.list_display_area_start_y + self.list_display_height - 1, 
            UserInterface.WORDS_PAD_RIGHT_MARGIN + self.words_pad_width -1 # smaxcol
        )
        
        # Scroll offsets are clamped in update_letters/update_words methods.
        # self.screen.refresh() # Refresh after all updates if needed, or handled by main loop redraw
        return True


    def get_window(self, name):
        # Pads are handled separately. get_window is for fixed windows.
        if name not in self.windows:
            # This implies a window needs to be created that wasn't handled by handle_resize.
            # For this refactor, all fixed windows are created in handle_resize.
            # So, if this is called for a fixed window, it means it might have been cleared.
            # However, create_ methods are designed to be callable multiple times.
            create_method = getattr(self, "create_"+name, None)
            if create_method is None:
                logger.error(f"No create method for window: {name}")
                # Potentially raise an error or return a dummy window
                return None # Or some dummy screen object
            logger.info(f"Recreating window {name} via get_window")
            func = create_method
            func()
        return self.windows.get(name) # Use .get for safety

    def get_string(self):
        # Ensure input window exists before trying to get string from it
        input_win = self.get_window("input")
        if input_win:
            return input_win.getstr().decode().lower()
        return "" # Fallback or raise error

    def create_greeting(self):
        # Uses GREETING_H, self.scr_width, at 0,0
        self.windows["greeting"] = curses.newwin(UserInterface.GREETING_H, self.scr_width, 0, 0)

    def update_greeting(self):
        pwin = self.get_window("greeting")
        if not pwin: return # Window might not exist if terminal is too small
        pwin.addstr(0,0, "Wordle Solver v0.0.1! Welcome!\n")
        pwin.noutrefresh()

    def create_progress(self):
        # Progress window y position is after greeting (GREETING_H)
        # Height is fixed at 3 for this example
        self.windows["progress"] = curses.newwin(3, self.scr_width, UserInterface.GREETING_H, 0)

    def update_progress(self, current, total):
        pwin = self.get_window("progress")
        if not pwin: return
        _, width = pwin.getmaxyx()
        pwin.addstr(0, 0, f"{current} / {total} | {current / total*100:.3f}%")
        progress_bar_width = max(0, width - 2) # Ensure positive width for progress bar
        progress = "#" * ((progress_bar_width * current) // total if total > 0 else 0)
        pwin.addstr(1, 0, f"[{progress:<{progress_bar_width}}]") # Display progress bar within brackets
        pwin.noutrefresh()
    
    def create_status(self):
        status_y_start = UserInterface.GREETING_H + UserInterface.TABS_H
        self.windows["status"] = curses.newwin(UserInterface.STATUS_H, self.scr_width, status_y_start,0)

    def update_status(self, hint):
        pwin = self.get_window("status")
        if not pwin: return
        pwin.clear()
        if hint is not None:
            pwin.addstr(0,0,"Current hints:")
            pwin.addstr(1,0,f"word size = {hint.size}") 
            pwin.addstr(2,0,f"correct =  {word_places(hint.corrects)}") 
            pwin.addstr(3,0,f"includes = {word_places(hint.includes)}") 
            pwin.addstr(4,0,f"excludes = {word_places(hint.excludes)}") 
        pwin.noutrefresh()

    def create_letters(self):
        # Pads are created in handle_resize if not already existing.
        # This method is now passive as per refactoring plan.
        pass

    def update_letters(self, stats):
        if self.list_area_is_too_small or self.letters_pad is None: return

        self.letters_pad.clear()
        lines_written = 0
        
        prefix = "> " if self.active_list == "letters" else "  "
        title = f"{prefix}Letters %:"
        try:
            self.letters_pad.addstr(lines_written, 0, title)
            lines_written += 1

            if stats is not None:
                for k, v in stats:
                    if lines_written >= self.letters_pad.getmaxyx()[0]: # Pad internal height
                        self.letters_pad.resize(lines_written + 20, UserInterface.LETTERS_PAD_FIXED_WIDTH)
                    self.letters_pad.addstr(lines_written, 0, f"{k}: {v:.4f}%")
                    lines_written += 1
            
            # Clamping scroll offset
            pad_content_height = lines_written
            max_scroll = max(0, pad_content_height - self.list_display_height)
            self.letters_scroll_offset = max(0, min(self.letters_scroll_offset, max_scroll))

            self.letters_pad.refresh(self.letters_scroll_offset, 0, 
                                     self.letters_pad_viewport_coords[0], self.letters_pad_viewport_coords[1],
                                     self.letters_pad_viewport_coords[2], self.letters_pad_viewport_coords[3])
        except curses.error as e:
            logger.error(f"Error updating letters_pad: {e}")


    def create_words(self):
        # Pads are created in handle_resize if not already existing.
        # This method is now passive as per refactoring plan.
        pass

    def update_words(self, bestwords):
        if self.list_area_is_too_small or self.words_pad is None: return

        self.words_pad.clear()
        lines_written = 0
        prefix = "> " if self.active_list == "words" else "  "
        
        try:
            if bestwords is not None:
                title = f"{prefix}Best of {len(bestwords)} words: {'score':>10} {'freq':>9}"
                self.words_pad.addstr(lines_written, 0, title)
                lines_written +=1
                
                for k, w_tuple in enumerate(bestwords):
                    if lines_written >= self.words_pad.getmaxyx()[0]: # Pad internal height
                        self.words_pad.resize(lines_written + 50, self.words_pad_width)
                    self.words_pad.addstr(lines_written, 0, f'{k+1:2}: {w_tuple[0]:20} {w_tuple[1]: 6.2f} {w_tuple[2]: .2E}')
                    lines_written += 1
            else:
                self.words_pad.addstr(lines_written, 0, f"{prefix}No words to display.")
                lines_written += 1

            pad_content_height = lines_written
            max_scroll = max(0, pad_content_height - self.list_display_height) 
            self.words_scroll_offset = max(0, min(self.words_scroll_offset, max_scroll))
            
            self.words_pad.refresh(self.words_scroll_offset, 0,
                                   self.words_pad_viewport_coords[0], self.words_pad_viewport_coords[1],
                                   self.words_pad_viewport_coords[2], self.words_pad_viewport_coords[3])
        except curses.error as e:
            logger.error(f"Error updating words_pad: {e}")


    def add_list(self, win, current, all):
        if not win: return # Safety check if window doesn't exist
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
        input_y_start = self.scr_height - UserInterface.INPUT_H
        self.windows["input"] = curses.newwin(UserInterface.INPUT_H, self.scr_width, input_y_start, 0)

    def update_input(self, func):
        pwin = self.get_window("input")
        if not pwin: return
        options = ["[c]orrect","[i]nclude","[e]xclude","[s]ize","[t]ab","[n]ext","so[r]t","[q]uit"]
        pwin.clear()
        self.add_list(pwin, func, dict(zip(self.funcs,options)))
        pwin.noutrefresh()

    def create_tabs(self):
        # Tabs window y position is after greeting (GREETING_H)
        self.windows["tabs"] = curses.newwin(UserInterface.TABS_H, self.scr_width, UserInterface.GREETING_H, 0)

    def update_tabs(self, current, all_tabs):
        pwin = self.get_window("tabs")
        if not pwin: return
        pwin.clear()
        pwin.addstr("TABS: ")
        self.add_list(pwin, current, all_tabs)
        pwin.noutrefresh()

    def clear_screen(self): # Renamed from 'clear' to be more specific
        self.screen.clear()
        self.screen.refresh()

    def update_main_ui(self,currnet_tab, all_tabs, hint, stats, bestwords):
        # This method assumes that handle_resize has confirmed the screen is usable
        # and list_area_is_too_small is False.
        # The main loop should check should_draw_main_ui before calling this.
        
        self.screen.clear() # Clear before full redraw

        self.update_greeting()
        self.update_tabs(currnet_tab, all_tabs)
        self.update_status(hint)
        self.update_letters(stats)
        self.update_words(bestwords)
        # self.update_input() will be called from main loop's needs_redraw block
        # No self.screen.refresh() or curses.doupdate() here.
        # Pad refreshes (letters_pad.refresh, words_pad.refresh) are done within their update methods.


    def update_loading_screen(self, current, total):
        # This method can be called even if the terminal is generally too small,
        # as it uses minimal layout.
        # However, handle_resize might have already displayed a "too small" message.
        # For simplicity, we'll let it try to draw.
        
        # A more robust approach might involve check_terminal_size_and_display_message
        # at the start of this method too, or ensuring handle_resize is called first.

        self.screen.clear()
        self.update_greeting() # Greeting is simple and usually fits
        self.update_progress(current, total) # Progress also simple
        self.screen.refresh()


    def get_args(self):
        input_win = self.get_window("input")
        if not input_win: return "" # Or raise error
        
        curses.echo() 
        args = input_win.getstr().decode().lower()
        curses.noecho() 
        
        input_win.clear() 
        input_win.noutrefresh() # Changed from refresh to noutrefresh
        return args

def main():
    ui = UserInterface()
    curses.noecho() 

    # Initial resize handling and setup
    should_draw_main_ui = ui.handle_resize()
    needs_redraw = True # Flag to trigger redraw, useful after certain operations

    num_lines = sum(1 for _ in open(sys.argv[1]))
    worddict = WordDict()
    # Only show loading if initial setup allows (not "Terminal too small")
    if should_draw_main_ui: # A basic check, could be more nuanced
        with open(sys.argv[1], "r") as file:
            for idx, line in enumerate(file):
                # Check if still okay to draw, in case of resize during loading
                if ui.scr_height < UserInterface.MIN_TERMINAL_HEIGHT or \
                   ui.scr_width < UserInterface.MIN_TERMINAL_WIDTH:
                    ui.check_terminal_size_and_display_message("Terminal too small during loading.")
                    # Potentially break or exit if loading cannot be shown
                    break 
                ui.update_loading_screen(idx+1, num_lines)
                word = line.strip()
                worddict.push(word)
    else: # Terminal was too small on startup
        # Load data silently or exit, as UI cannot display loading.
        # For now, just load silently if it was only the list area that was too small initially.
        # If MIN_TERMINAL_HEIGHT/WIDTH failed, then getch loop won't run meaningfully.
        logger.info("Terminal too small for loading screen, loading data silently.")
        for line in open(sys.argv[1]): worddict.push(line.strip())

    if should_draw_main_ui: ui.clear_screen()


    freq = [ a.split() for a in open(sys.argv[2]) ]
    freq = {a[0] : float(a[1]) for a in freq}

    tabs = {"0": HintConfig(0)}
    current_tab = "0"
    result = None
    stats = None
    sorting_strategy = 2
    active_command = None
    RESIZE_DEBOUNCE_DELAY = 0.25
    last_resize_time = 0.0

    while True:
        if should_draw_main_ui:
            if needs_redraw: # Only redraw if necessary
                current_hint = tabs[current_tab]
                result = worddict.apply_filter(current_hint)
                stats, bestwords = calc_stats(result, freq, sorting_strategy)
                
                ui.update_main_ui(current_tab, tabs.keys(), current_hint, stats, bestwords)
                # update_input is also part of the main UI update sequence
                ui.update_input(active_command) 
                
                curses.doupdate() # Single call to update physical screen for all noutrefreshes
                needs_redraw = False # Reset flag after redraw
            
        else:
            # If UI shouldn't be drawn (e.g. terminal too small), handle_resize has already
            # cleared and displayed a message and called screen.refresh().
            # No further screen operations needed here until should_draw_main_ui is true.
            # We might need to call handle_resize here if a resize could make it drawable again.
            # For now, a simple clear might be okay, or rely on getch timeout for resize event.
            pass


        ui.screen.timeout(100) 
        key = ui.screen.getch()

        # Always allow quit and resize, even if main UI is not drawn
        if key != -1 and key < 256 and chr(key) == 'q':
             break
        elif key == curses.KEY_RESIZE:
            current_time = time.time()
            if (current_time - last_resize_time) < RESIZE_DEBOUNCE_DELAY:
                continue
            last_resize_time = current_time
            
            should_draw_main_ui = ui.handle_resize()
            needs_redraw = True # Force redraw after resize
            active_command = None # Clear any pending command
            continue # Restart loop to check should_draw_main_ui

        if not should_draw_main_ui:
            # If not drawable, skip other input processing until resize makes it drawable
            if key != -1 : logger.info(f"Terminal too small, input {key} ignored.")
            continue

        # Process other inputs only if UI is drawable
        if key == curses.KEY_LEFT or key == curses.KEY_RIGHT:
            if ui.active_list == "words": ui.active_list = "letters"
            else: ui.active_list = "words"
            active_command = None
            needs_redraw = True
        elif key == curses.KEY_UP:
            if ui.active_list == "letters": ui.letters_scroll_offset = max(0, ui.letters_scroll_offset - 1)
            elif ui.active_list == "words": ui.words_scroll_offset = max(0, ui.words_scroll_offset - 1)
            active_command = None
            needs_redraw = True
        elif key == curses.KEY_DOWN:
            if ui.active_list == "letters": ui.letters_scroll_offset += 1 
            elif ui.active_list == "words": ui.words_scroll_offset += 1 
            active_command = None
            needs_redraw = True
        elif key != -1 and key < 256 and chr(key) in ui.funcs:
            func_char = chr(key).lower()
            active_command = func_char
            
            # Update input to show the command character immediately
            ui.update_input(active_command)
            args = ui.get_args() # This call now includes its own clear and refresh for input line
            active_command = None # Clear active command after getting args
            needs_redraw = True # Assume command changes data

            try:
                current_hint = tabs[current_tab] # Ensure current_hint is up-to-date
                if func_char == "s":
                    size = int(args)
                    tabs[current_tab] = HintConfig(size)
                    ui.words_scroll_offset = 0; ui.letters_scroll_offset = 0; ui.active_list = "words" 
                elif func_char == "c":
                    if "#" in args: current_hint.clear_corrects()
                    else: 
                        for k_arg, v_arg in split_args(current_hint.size, args).items(): current_hint.correct(k_arg, v_arg)
                elif func_char == "i":
                    if "#" in args: current_hint.clear_includes()
                    else:
                        for k_arg, v_arg in split_args(current_hint.size, args).items(): current_hint.include(k_arg, v_arg)
                elif func_char == "e":
                    args = args.replace(" ", "")
                    if "#" in args: current_hint.clear_excludes()
                    else: 
                        for l_arg in set(args): current_hint.exclude(l_arg)
                elif func_char == "n": 
                    if args != "":
                        try: ui.words_scroll_offset = max(0, int(args) - 1) 
                        except ValueError: logger.warn(f"Invalid arg for 'n': {args}")
                    else: ui.words_scroll_offset = 0 
                elif func_char == "r": 
                    if args in ["0","1","2"]: sorting_strategy = int(args)          
                elif func_char == "t": 
                    if args in tabs: current_tab = args
                    else: tabs.update({args: copy.copy(current_hint)}); current_tab = args
            except Exception as e:
                logger.error(f"Cmd error {func_char} with {args}: {e} {traceback.format_exc()}")
        elif key == -1: # Timeout
            pass # No input, just continue (allows loop to check needs_redraw if set by something else)
        else: # Other unhandled key
            logger.info(f"Unhandled key: {key}")


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