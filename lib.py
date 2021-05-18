#!/usr/bin sage
import os
import sys
import traceback

import fire

import sympy

import random

import time
from datetime import timedelta

import bisect

from collections import deque

import multiprocessing

from collections import OrderedDict

from sage.all import *

sys.path.append(os.path.dirname(__file__) + "/estimate-all-the-lwe-ntru-schemes.github.io")
from estimator import estimator

# TODO: logging