__version__ = "0.1.0"
__author__ = "Nicolai Krebs"

import sys
import os

file = os.path.abspath(__file__)
here = os.path.dirname(file)

there = os.path.join(here, "estimate_all_schemes")

sys.path.append(here)
sys.path.append(there)