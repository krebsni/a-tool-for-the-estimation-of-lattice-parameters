import os
import sys
import sphinx_rtd_theme

sys.path.insert(0, os.path.abspath('..'))

project = "A Tool for the Estimation of Lattice Parameters"
author = "Nicolai Krebs"
html_theme = "sphinx_rtd_theme"

extensions = ['sphinx.ext.autodoc', 'sphinx_rtd_theme','sphinx.ext.mathjax', 'sphinxcontrib.bibtex', 'sphinx.ext.autosectionlabel',]
autoclass_content = 'both'
bibtex_bibfiles = ['../thesis/bibliography.bib']
bibtex_default_style = 'alpha'
autosectionlabel_prefix_document = True