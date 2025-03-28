import sys
import pickle
import os
import copy
import time
import itertools
import json
from itertools import chain, combinations

from sortedcontainers import SortedList, SortedDict, SortedSet

first_rank = {
'e': 11.794077134986226,
's': 9.35757239803803,
'i': 8.127561647517302,
'a': 7.8147046966337435,
'r': 7.289356984478935,
'n': 6.155932943626957,
'o': 6.14165490828462,
't': 6.080763286971712,
'l': 5.679298528522475,
'd': 3.9571155009070753,
'c': 3.7912383256063964,
'u': 3.485940334609958,
'g': 2.930356782906672,
'p': 2.8333501310219713,
'm': 2.764899549821944,
'h': 2.3537761204058323,
'b': 2.176140563058523,
'y': 1.533628972653363,
'f': 1.439981858496271,
'k': 1.2329503460323858,
'w': 1.0553147886850769,
'v': 0.9675468655513001,
'z': 0.39222602969831355,
'x': 0.28850030235839547,
'q': 0.18225492172277094,
'j': 0.17385607740374925,
}

def sorting_func(container, x):
    w = container[x]
    return (len(w), w)

def powerset(iterable):
    # powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)
    s = list(iterable)
    return reversed(list(chain.from_iterable(combinations(s, r) for r in range(len(s)+1))))

class WordDict:
    def __init__(self):
        self.idx = 0


        self.sfunc = lambda x : sorting_func(self.data, x)
    def __init__(self, pickledata = None):
        self.idx = 0
        
        if pickledata != None:
            self.data = pickledata['data']
            self.sfunc = lambda x : sorting_func(self.data, x)
            self.lists = { k : SortedList(v,self.sfunc) for k,v in pickledata['lists'].items()}
            self.letters = SortedDict({ k : SortedList(v,self.sfunc) for k,v in pickledata['letters'].items()})
        else:
            self.data = dict()
            self.sfunc = lambda x : sorting_func(self.data, x)
            self.lists = dict()
            self.letters = SortedDict()

        

    def get_pickledata(self):
        return{'data':self.data, 'lists' : self.convert_idxs(self.lists), 'letters' : self.convert_idxs(self.letters)}

    def push(self, word):
        
        size = len(word)
        self.data[self.idx] = word
        
        if size in self.lists:
            self.lists[size].add(self.idx)
        else:
            self.lists[size] = SortedList(iterable = [self.idx], key = self.sfunc)

        for idx, l in enumerate(word):
            key = (l, idx)
            if key in self.letters:
                self.letters[key].add(self.idx)
            else:
                container = SortedList(iterable = [self.idx], key = self.sfunc)
                self.letters[key] = container

        self.idx += 1
    
    def get_idxs(self, container):
        ret = []
        for idx in container:
            ret.append(idx)
        return ret
    
    def convert_idxs(self, container):
        ret = {}
        for k,v in container.items():
            ret[k] = self.get_idxs(v)
        return ret

    def get_words(self, container):
        ret = []
        for idx in container:
            ret.append(self.data[idx])
        return ret

    def getitem_size(self, key):
        if key not in self.lists:
            return SortedList()
        else:
            ret = self.get_words(self.lists[key])
            return ret

    def filter_substr(self, init_set, value):
        if len(value[0]) == 1:
            if value in self.letters:
                filtered_values = SortedSet(iterable = self.letters[value], key = self.sfunc)
                init_set = init_set.intersection(filtered_values)
        else:
            word = value[0]
            init = value[1]
            for (idx, l) in enumerate(word):
                key = (l,init+idx)
                if key in self.letters:
                    filtered_values = SortedSet(iterable = self.letters[key], key = self.sfunc)
                    init_set = init_set.intersection(filtered_values)
        return init_set



    def getitem_dict(self, config):
        filtered_set = SortedSet(iterable = self.data.keys(), key = self.sfunc)


        if 'size' in config and config['size'] >= 1:
            filtered_values = SortedSet(iterable = self.lists[config['size']], key = self.sfunc)
            filtered_set = filtered_set.intersection(filtered_values)
            positionals = set(range(config['size']))
        else:
            max_size = max(self.lists.keys())
            positionals = set(range(max_size))

        # print("POS: ", positionals)

        if 'substr' in config:
            
            for p in config['substr']:
                for (idx, l) in enumerate(p[0]):
                    pos = p[1] + idx
                    positionals.remove(pos)
                filtered_set = self.filter_substr(filtered_set, p)

        # print("POS: ", positionals, config)
        
        # ret = SortedSet(iterable = [], key = self.sfunc)
        if 'letters' in config:
            filters = []
            
            for l in config['letters']:
                with_letter = SortedSet(iterable = [], key = self.sfunc)
                for p in positionals:
                    init_set = filtered_set.copy()
                    init_set = self.filter_substr(init_set, (l, p))
                    with_letter = with_letter.union(init_set)
                filters.append(with_letter)
            filtered_set = filtered_set.intersection(*filters)

        if 'not' in config:
            filters = []
            for key in itertools.product(config["not"], positionals):
                init_set = filtered_set.copy()
                init_set = self.filter_substr(init_set, key)
                filters.append(init_set)
            filtered_set.difference_update(*filters)

        ret = []
        if 'using' in config:
            letters = config['using'][0]
            matches = config['using'][1]

            for sub in powerset(letters):
                if matches <= len(sub) <= len(positionals):
                    filters = []
                    for l in sub:
                        with_letter = SortedSet(iterable = [], key = self.sfunc)
                        for p in positionals:
                            init_set = filtered_set.copy()
                            init_set = self.filter_substr(init_set, (l, p))
                            with_letter = with_letter.union(init_set)
                        filters.append(with_letter)
                    ret = ret + self.get_words(filtered_set.intersection(*filters))

        # if 'letters' in config:
        #     print("letters!")
        #     for key in itertools.product(config['letters'], positionals):
        #         print("KEY = ", key)
        #         if key in self.letters:
        #             filtered_values = SortedSet(iterable = self.letters[key], key = self.sfunc)
        #             filtered_temp = filtered_set.intersection(filtered_values)
        #             print(key, len(filtered_temp))
        #             ret = ret.union(filtered_temp)

        if len(ret) == 0:
            ret = self.get_words(filtered_set)
        
        return ret

    def __getitem__(self, key):
        if isinstance(key, int):
            return self.getitem_size(key)
        if isinstance(key, dict):
            return self.getitem_dict(key)




def main():
    start = time.time()

    fname = "dict.dat"
    if os.path.isfile(fname):
        file = open(fname, "rb")
        worddict = WordDict(pickledata = pickle.load(file))
        file.close()
    else:
        worddict = WordDict()
        with open(sys.argv[1], 'r') as file:
            # Read each line in the file
            for line in file:
                # Print each line
                word = line.strip()
                worddict.push(word)
        file = open(fname, "wb")
        ddd = worddict.get_pickledata()
        print(type(ddd))
        pickle.dump(ddd, file)
        file.close()
        print("INIT DONE")
    end = time.time()
    print("Elapsed time: ", end - start)
    
    for i in range(20):
        print(i, len(worddict[i]))
    
    # start = time.time()
    # filt = {'size':-5, 'substr' : [('b',1),('e',2)]}
    # end = time.time()
    # ret = worddict[filt]
    # print(len(ret), ret)
    # print("FILT DONE: ", end - start)
    
    # start = time.time()
    # filt = {'size':5, 'substr' : [('c',1)]}
    # end = time.time()
    # ret = worddict[filt]
    # print(len(ret), ret)
    # print("FILT DONE: ", end - start)

    # start = time.time()
    # filt = {'size':5, 'substr' : [('c',1)], 'letters': 'sh'}
    # end = time.time()
    # ret = worddict[filt]
    # print(len(ret), ret)
    # print("FILT DONE: ", end - start)

    while True:
        rank = first_rank
        filt = eval(input("Enter filter:"))
        print(filt)
        ret = worddict[filt]
        if len(ret) > 20:
            print(len(ret))

            letters = dict()
            cnt = 0
            for word in ret:
                for l in word:
                    cnt += 1
                    if l in letters:
                        letters[l] += 1
                    else:
                        letters[l] = 1
            sletters = sorted([(k, v / cnt * 100) for k,v in letters.items()], key = lambda x: -x[1])
            for s in sletters:
                print(s[0], s[1], "%")
            rank = {a[0] : a[1]/100 for a in sletters}
        bestlist = SortedList(key = lambda x: -x[1])
        for w in ret:
            ws = sorted(set(w))
            score = 0
            for l in ws:
                score += rank[l]
            bestlist.add((w,score))
        for p in bestlist[:5]:
            print(f"WORD = {p[0]:>20} {p[1]:.2f}%")



if __name__ == "__main__":
    main()
