import morfeusz2 as mf
import sys

morf = mf.Morfeusz()

def main():
    
    output_dictionary = set()
    num_lines = sum(1 for _ in open(sys.argv[1]))
    
    with open(sys.argv[1], 'r') as file:
        # Read each line in the file
        for idx, line in enumerate(file):
            print(f"{idx+1} / {num_lines}", end="\r")
            # Print each line
            word = line.strip()
            ret = morf.analyse(word)
            for r in ret:
                lexem = r[2][1].split(":")[0]
                output_dictionary.add(lexem.lower())
    
    print(num_lines, " -> ", len(output_dictionary))

    with open(sys.argv[2], 'w') as file:
        for word in sorted(list(output_dictionary)):
            file.write(word+"\n")
        
if __name__ == "__main__":
    main()