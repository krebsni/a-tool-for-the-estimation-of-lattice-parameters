import os
import sys
sys.path.insert(0, os.path.abspath('..'))

project = "A Tool for the Estimation of Lattice Parameters"
author = "Nicolai Krebs"

extensions = ['sphinx.ext.autodoc', 'sphinx.ext.mathjax', 'sphinxcontrib.bibtex']
autoclass_content = 'both'
bibtex_bibfiles = ['../Thesis/bibliography.bib']
bibtex_default_style = 'alpha'

