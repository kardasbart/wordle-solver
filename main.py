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
import curses.textpad
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
    def __init__(self, word_len):
        self.word_len = word_len
        self.data = dict()
        self.cnt = 0

    def push(self, word):
        if len(word) != self.word_len:
            raise WordLenException()
        idx = self.cnt
        self.cnt += 1
        self.data[idx] = word
        return idx

    def get(self, idx):
        return self.data[idx]


class WordDict:
    def __init__(self):
        self.storage = dict()
        self.letter_sets = dict()
        self.letter_lookup = dict()
        self.word_sets = dict()

    def push(self, word):
        size = len(word)
        if size not in self.storage:
            self.storage[size] = WordStorage(size)
        idx = self.storage[size].push(word)

        if size not in self.word_sets:
            self.word_sets[size] = SortedSet()
        self.word_sets[size].add(idx)

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

    def apply_filter(self, size, rules):
        init_set = self.word_sets[size]
        for mode, key, func in rules:
            if mode == "simple":
                init_set = self.filter(init_set, key, func)
            elif mode == "include":

                filtered = self.letter_lookup[(size, key)]
                logger.info(f"FILTER SIZE = {len(filtered)}")
                logger.info(f"INIT SIZE = {len(init_set)}")
                init_set = init_set.intersection(filtered)
                logger.info(f"AFTER INIT SIZE = {len(init_set)}")

        ret = [self.storage[size].get(idx) for idx in init_set]
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
    bestlist = SortedList(key=lambda x: -x[1])

    for w in result:
        ws = sorted(set(w))
        score = 0
        for l in ws:
            score += rank_dict[l]
        bestlist.add((w, score))

    return rank, bestlist


def print_filter_result(screen, result, idx_next):
    stats, bestwords = calc_stats(result)
    screen.addstr(f"\n\nWords left: {len(bestwords)}\n\n")
    screen.addstr("Letters occurences according to filter:\n")
    for k, v in stats:
        screen.addstr(f"{k}: {v:.4f}%\n")

    screen.addstr("\nBest words:\n")
    maxw = len(bestwords)
    for k, w in enumerate(bestwords[min(idx_next, maxw) : min(idx_next + 10, maxw)]):
        screen.addstr(f'{k+1+idx_next}: "{w[0]}" score = {w[1]:.2f}\n')


def print_state(screen, hints, result, idx_next):
    screen.clear()
    screen.addstr("Wordle Solver v0.0.1! Welcome!\n\n")
    screen.addstr("Current hints:\n")
    if hints is not None:
        screen.addstr(f"word size = {hints.size}\n")
        screen.addstr(f"correct = {hints.corrects}\n")
        screen.addstr(f"includes = {hints.includes}\n")
        screen.addstr(f"excludes = {hints.excludes}\n\n")
        if result is not None:
            print_filter_result(screen, result, idx_next)
    else:
        screen.addstr("word size = ?\n")
    screen.refresh()


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


def main():
    start = time.time()

    screen = curses.initscr()
    curses.curs_set(0)
    height, width = screen.getmaxyx()

    num_lines = sum(1 for _ in open(sys.argv[1]))
    worddict = WordDict()
    with open(sys.argv[1], "r") as file:
        # Read each line in the file
        for idx, line in enumerate(file):
            screen.addstr(0, 0, f"{idx} / {num_lines} | {idx / num_lines*100:.3f}%")
            progress = "#" * ((width * idx) // num_lines)
            screen.addstr(1, 0, f"{progress}")
            screen.refresh()
            # Print each line
            word = line.strip()
            worddict.push(word)

    current_hint = None
    idx_next = 0
    while True:
        if current_hint is None:
            print_state(screen, current_hint, None, idx_next)
            screen.addstr("Set word length:")
            event = screen.getstr().decode()
            size = int(event)
            # size = 5
            current_hint = HintConfig(size)
            idx_next = 0
        else:
            result = worddict.apply_filter(current_hint.size, current_hint.rules())
            print_state(screen, current_hint, result, idx_next)

            func = chr(screen.getch())
            if func == "q":
                break
            args = screen.getstr().decode()
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
                    idx_next = int(args)
            except:
                pass

    y, x = screen.getyx()
    screen.addstr(y, 0, "Bye!\n")
    screen.refresh()


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
