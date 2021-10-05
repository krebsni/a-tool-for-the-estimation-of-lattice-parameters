# N = random_prime(2^150)*random_prime(2^150)
# message = Integer('thepasswordfortodayisswordfish',base=35)
# c = message^3 % N
# a = Integer('thepasswordfortodayis000000000',base=35)
# X = Integer('0',base=35)
# M = matrix([[X^3, 3*X^2*a, 3*X*a^2, a^3-c],
# [0,N*X^2,0,0],[0,0,N*X,0],[0,0,0,N]])
# B = M.LLL()
# Q = B[0][0]*x^3/X^3+B[0][1]*x^2/X^2+B[0][2]*x/X+B[0][3]
# Q.roots(ring=ZZ)[0][0].str(base=35)

# def next_parameters(x,y,z):
#     yield x+1,y+1,z+1
#     yield x+1,y-1,z+1

# def cost(x,y,z):
#     return x+y+z

# current_parameter_sets = [(1,1,1)]
# current_parameter_sets = [x for p in current_parameter_sets for x in next_parameters(*p)] 
# current_parameter_sets.sort(key=lambda x : cost(*x))
# print(current_parameter_sets)
# import numpy as np
# def f(x, y):
#     return x+y

# x = np.array([i for i in range(20)])
# y = np.array([i for i in range(20)])
# # X, Y = np.meshgrid(x, y)
# # print(X)
# # print(Y)
# # z = np.array(f(np.ravel(X), np.ravel(Y)))
# # print(z)
# # print(z.reshape(X.shape))
# print(f(x, y))

# import bisect 

# costs = [1, 2, 3, 3, 4]
# parameters = [5, 3, 6, 6, 5]

# cost = 3
# parameter_set = 5

# i = bisect.bisect_right(costs, cost)
# print(i)

# # only insert if not duplicate
# temp = cost
# while i > 0:
#     if costs[i-1] == cost and parameters[i-1] != parameter_set:
#         i -= 1
#     elif parameters[i-1] != parameter_set:
#         costs.insert(i, cost)
#         parameters.insert(i, parameter_set)
#         break
#     else:
#         break

# import multiprocessing as mp
# import os, time

# def f(n):
#     sum = 0
#     for i in range(10000000000**n):
#         sum += i
#     return sum

# def g():
#     print("Success!")

# n_procs = os.cpu_count()
# pool = mp.Pool(processes=2)
# async_res = []

# for i in range(2):
#     async_res.append(pool.apply_async(func=f, args=(i)))

# start = time.time()
# while time.time() - start < 1:
#     print("waiting...")
#     time.sleep(0.1)
#     for r in async_res:
#         try:
#             if r.successful():
#                 print("Result ready. Sum: " + str(r.get()))

#         except ValueError:
#             print("Result not ready yet")

# pool.terminate()
# pool.apply(g)
# time.sleep(2)
from enum import Enum
class RowSamplingType(Enum):
    RANDOM = "Randomly"
    FIRST_N = "First n (Number of Rows)"

x = RowSamplingType.RANDOM
y = x.value
if y == x.value:
    print("Yeah!")
import random
print(random.randrange(9))