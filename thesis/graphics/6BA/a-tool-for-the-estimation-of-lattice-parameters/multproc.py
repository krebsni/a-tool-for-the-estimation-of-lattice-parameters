import multiprocessing as mp
from concurrent.futures import ThreadPoolExecutor
from queue import Empty
import time
import os
import random

class Result():
    def __init__(self, is_secure, res):
        self.is_secure = is_secure
        self.res = res

    def __str__(self):
        return str(self.is_secure) + " " + str(self.res)

def terminator(f):
    def wrapper(job_args):
        alg, n, ter = job_args
        q = mp.Queue()
        p = mp.Process(target=f, args=(q, alg, n))
        p.start()
        print(str(p.pid) + " started...")
        while(True):
            try:
                # read termination signal from queue if available, else Empty exception
                ter.get(block=True, timeout=0.1)
                print(str(p.pid) + " terminator received termination signal. Terminate and forward")
                # put it back in queue to terminate all other processes
                ter.put(False)
                # terminate process
                p.terminate() # TODO: do we need to handle SIGTERM signal?
                p.join()
                q.close()
                return "unsuccessful"
            except Empty:
                pass
            try:
                res = q.get(block=False)
                # result available, evaluate
                if res.is_secure:
                    print(str(p.pid) + " terminator received secure result")
                    # all good, other processes continue
                    p.join()
                    q.close()
                    return str(res)
                else: 
                    print(str(p.pid) + " terminator received insecure result. Send termination signal")
                    # not secure => terminate all other processes
                    # send termination signal. Signal is read by one, resent, ... until all are terminated
                    ter.put(False)
                    p.terminate()
                    p.join()
                    q.close()
                    return str(res) 
            except Empty:
                pass
    return wrapper


@terminator
def job(q, alg, n):
    sum = 0
    alg(n)
    for i in range(10000000000):
        sum = i
        if random.random() < 0.00001:
            print(os.getpid(), "Not secure. i=", i)
            q.put(Result(is_secure=False, res={"alg": alg, "sum": str(sum)}))
        
    print(os.getpid(), "Secure")
    q.put(Result(is_secure=True, res={"alg": alg, "sum": str(sum)}))


def a1(n):
    print(os.getpid(), "Running a1: ", n)

def a2(n):
    print(os.getpid(), "Running a2: ", n)

def a3(n):
    print(os.getpid(), "Running a3: ", n)

def a4(n):
    print(os.getpid(), "Running a4: ", n)

def main():
    algs = [a1, a2, a3, a4]
    NUM_CPUS = mp.cpu_count()
    print(NUM_CPUS)
    tp = ThreadPoolExecutor(NUM_CPUS)

    n = 5
    ter = mp.Queue()
    data = [(x, n, ter) for x in algs]
    for res in tp.map(job, data):
        print("Result: " + res)