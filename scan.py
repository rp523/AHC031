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
    score_sum = 0
    score_norm = 0
    min_score = -1
    min_score_idx = -1
    for i in range(10):
        cmd = "./tester ./target/release/start < in/{0:04d}.txt > out/{0:04d}.txt".format(i, i)
        ret = subprocess.getoutput(cmd)

        for line in ret.split("\n"):
            found = line.find(key)
            if found != 0:
                continue
            score = int(line[len(key):])
            score_sum += score
            score_norm += 1
            if min_score < 0:
                min_score = score
                min_score_idx = i
            elif min_score > score:
                min_score = score
                min_score_idx = i
        print("---------[{}]".format(i), score, min_score, min_score_idx, score_sum / score_norm * 50 / 1000000000)
        print(ret)
    print("sum: ", score_sum / score_norm * 50 / 1000000000)
if __name__ == "__main__":
    main()