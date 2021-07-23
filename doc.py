import fire
import os
if __name__ == "__main__":
    # estimation_example()
    class Commandline:
        def doc(self):
            # requires sphinx (e.g. "pip install sphinx")
            os.system("sphinx-apidoc -o doc lattice_parameter_estimation usage_example.py") # EXCLUDE usage_example for now as it does not "compile" at all
            os.system("sphinx-build doc doc/html")

    fire.Fire(Commandline)