#coding: utf-8
from tqdm import tqdm
import subprocess

def main():
    '''
    cargo build --release && ./tester ./target/release/start < in/0009.txt > out.txt
    '''
    ini_cmd = "cargo build --release"
    subprocess.getoutput(ini_cmd)
    key = "Score = "
    for i in range(10):
        cmd = "./tester ./target/release/start < in/{0:04d}.txt > out/{0:04d}.txt".format(i, i)
        ret = subprocess.getoutput(cmd)

        for line in ret.split("\n"):
            found = line.find(key)
            if found != 0:
                continue
            score = int(line[len(key):])
            print(i, score)
        #print("{}\n".format(i), ret)
if __name__ == "__main__":
    main()