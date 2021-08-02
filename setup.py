from setuptools import setup
from lib2to3.main import main as two_to_three
from subprocess import check_call

import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
sys.path.append(here)


import lattice_parameter_estimation

check_call("git submodule update --init --recursive".split())

estimator = "lattice_parameter_estimation/estimator/estimator.py"
estimator_init = "lattice_parameter_estimation/estimator/__init__.py"

# Fix old python version in estimator
# Existice of backup file used as indicator that fix happened
if not os.path.exists(f"{estimator}.bak"):
    # # prevent syntax errors from old python version
    # error = two_to_three("lib2to3.fixes", args=f"-w {estimator}".split())
    # if error != 0:
    #     sys.exit(error)

    # # fix error with not found __round__ on sage's RR
    # with open(estimator, "r") as f:
    #     content = f.read()
    # with open(estimator, "w") as f:
    #     content = content.replace(" step_size/2", "step_size//2")
    #     f.write(f"from sage.misc.functional import round # added to fix errors\n\n{content}")

    # make the estimator nicer to import
    with open(estimator_init, "w") as f:
        f.write("# -*- coding: utf-8 -*-\nfrom .estimator import * # noqa\n")

setup(
    name="lattice-parameter-estimation",
    version=lattice_parameter_estimation.__version__,
    packages=["lattice_parameter_estimation"],
    author=lattice_parameter_estimation.__author__,
    package_data={
        "": ["*/*.py", "*/*/*.py"]
    }
)
