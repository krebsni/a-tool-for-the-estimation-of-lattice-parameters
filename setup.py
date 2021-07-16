from setuptools import setup

from subprocess import check_call

import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
sys.path.append(here)


import lib

check_call("git submodule update --init --recursive".split())

estimator = "lib/estimate_all_schemes/estimator/estimator.py"
estimator_init = "lib/estimate_all_schemes/estimator/__init__.py"

# Fix old python version in estimator
# Existice of backup file used as indicator that fix happened
if not os.path.exists(f"{estimator}.bak"):
    # prevent syntax errors from old python version
    check_call(f"python -m lib2to3 -w {estimator}".split())

    # fix error with not found __round__ on sage's RR
    with open(estimator, "r") as f:
        content = f.read()
    with open(estimator, "w") as f:
        f.write(f"from sage.misc.functional import round # added to fix errors\n\n{content}")

    # make the estimator nicer to import
    with open(estimator_init, "w") as f:
        f.write("# -*- coding: utf-8 -*-\nfrom .estimator import * # noqa\n")

setup(
    name="lattice-parameter-estimation",
    version=lib.__version__,
    packages=["lib"],
    author=lib.__author__,
    package_data={
        "": ["*/*.py", "*/*/*.py"]
    }
)