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


# logger = logging.getLogger(__file__)
# hdlr = logging.FileHandler(__file__ + ".log")
# formatter = logging.Formatter("%(asctime)s %(levelname)s %(message)s")
# hdlr.setFormatter(formatter)
# logger.addHandler(hdlr)
# logger.setLevel(logging.DEBUG)


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
            return SortedSet()
        filtered = self.letter_sets[key]
        return bound_func(filtered)

    def apply_filter(self, config):
        if config.size not in self.words_by_size:
            init_set = SortedSet(self.storage.data.keys())
        else:
            init_set = self.words_by_size[config.size]
        
            for mode, key, func in config.rules():
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
        if -1 in positions:
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


def calc_stats(result):
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
    bestlist = SortedSet(key=lambda x: -x[1])

    for w in result:
        ws = sorted(set(w))
        score = 0
        for l in ws:
            score += rank_dict[l]
        bestlist.add((w, score))

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
        curses.curs_set(0)
        self.scr_height, self.scr_width = self.screen.getmaxyx()
        self.windows = dict()

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
        self.windows["status"] = curses.newwin(10,self.scr_width, 2,0)

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
        self.windows["letters"] = curses.newwin(40,15, 9,0)

    def update_letters(self, stats):
        pwin = self.get_window("letters")
        pwin.clear()
        if stats is not None:
            pwin.addstr("Letters %:\n")
            for k, v in stats:
                pwin.addstr(f"{k}: {v:.4f}%\n")
        pwin.refresh()

    def create_words(self):
        self.windows["words"] = curses.newwin(40,self.scr_width, 9, 20)

    def update_words(self, bestwords, idx_next):
        pwin = self.get_window("words")
        pwin.clear()
        if bestwords is not None:
            height, _ = pwin.getmaxyx()
            height -= 5
            pwin.addstr(f"Best of {len(bestwords)} words:\n")
            maxw = len(bestwords)
            for k, w in enumerate(bestwords[min(idx_next, maxw) : min(idx_next + height-1, maxw)]):
                pwin.addstr(f'{k+1+idx_next}: "{w[0]}" score = {w[1]:.2f}\n')
        pwin.refresh()

    def create_input(self):
        self.windows["input"] = curses.newwin(2,self.scr_width, 50, 0)

    def update_input(self, func):
        pwin = self.get_window("input")
        pwin.clear()
        options = ["[c]orrect","[i]nclude","[e]xclude","[s]ize","[n]ext","[q]uit"]
        for opt in options:
            if f"[{func}]" in opt:
                pwin.addstr(opt, curses.A_STANDOUT)
            else:
                pwin.addstr(opt)
            if opt != options[-1]:
                pwin.addstr(" | ")
        pwin.addstr("\n")
        pwin.refresh()

    def clear(self):
        self.screen.clear()

    def update_main(self, hint, stats, bestwords, idx_next):
        self.update_greeting()
        self.update_status(hint)
        self.update_letters(stats)
        self.update_words(bestwords, idx_next)

    def update_loading(self, current, total):
        self.update_greeting()
        self.update_progress(current, total)

    def get_func(self):
        pwin = self.get_window("input")
        curses.noecho()
        while True:
            func = chr(pwin.getch()).lower()
            if func in "ciesqn":
                break
        curses.echo()
        return func

    def get_args(self):
        pwin = self.get_window("input")
        args = pwin.getstr().decode().lower()
        pwin.clear()
        pwin.refresh()
        return args

def main():
    ui = UserInterface()

    num_lines = sum(1 for _ in open(sys.argv[1]))
    worddict = WordDict()
    with open(sys.argv[1], "r") as file:
        # Read each line in the file
        for idx, line in enumerate(file):
            ui.update_loading(idx+1, num_lines)
            word = line.strip()
            worddict.push(word)

    # freq = [ a.split() for a in open(sys.argv[2]) ]
    # freq = {a[0] : a[1] for a in freq}

    current_hint = HintConfig(0)
    result = None
    stats = None
    idx_next = 0
    while True:
        result = worddict.apply_filter(current_hint)
        stats, bestwords = calc_stats(result)
        ui.update_main(current_hint, stats, bestwords, idx_next)

        ui.update_input(None)
        func = ui.get_func()
        ui.update_input(func)
        if func == "q":
            break
        args = ui.get_args()
        try:
            if func == "s":
                size = int(args)
                current_hint = HintConfig(size)
            elif func == "c":
                for k, v in split_args(current_hint.size, args).items():
                    current_hint.correct(k, v)
            elif func == "i":
                for k, v in split_args(current_hint.size, args).items():
                    current_hint.include(k, v)
            elif func == "e":
                for l in set(args.replace(" ", "")):
                    current_hint.exclude(l)
            elif func == "n":
                if args != "":
                    idx_next = int(args)
                else:
                    idx_next = 0
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