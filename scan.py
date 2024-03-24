from pathlib import Path
from tqdm import tqdm
import os, shutil
from subprocess import getoutput
import time

def main():
    scan_bin_path = Path("scan")
    if scan_bin_path.exists():
        os.remove(scan_bin_path)
    getoutput("cargo build -r")
    build_bin_path = Path("target/release/atcoder")
    assert(build_bin_path.exists())
    shutil.copy(build_bin_path, scan_bin_path)
    dt_max = 0
    dt_max_i = -1
    for i in range(100):
        cmd = ""
        cmd += "./{}".format(scan_bin_path)
        cmd += " < tools/in/{0:04d}.txt".format(i)
        cmd += " > tools/out/{0:04d}.txt".format(i)
        t0 = time.time()
        print(cmd)
        getoutput(cmd)
        t1 = time.time()
        dt = t1 - t0
        if dt_max < dt:
            dt_max = dt
            dt_max_i = i
        print(dt, dt_max, dt_max_i)
if __name__ == "__main__":
    main()