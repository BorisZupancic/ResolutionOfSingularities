# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

import sys, os, warnings
import sage_package.sphinx
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
warnings.filterwarnings('ignore', category=DeprecationWarning)

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = 'Resolution Of Singularities'
copyright = '2026, Boris Zupancic'
author = 'Boris Zupancic'
release = '0.1'

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

extensions = [
    'sphinx.ext.autodoc',    # generates docs from docstrings
    'sphinx.ext.doctest',    # runs sage: examples as tests
    'sphinx.ext.mathjax',    # renders your LaTeX
    'sphinx.ext.viewcode',   # adds [source] links to methods
    'sphinx.ext.napoleon',   # supports Google/NumPy style docstrings (optional but nice)
    'sphinx.ext.intersphinx',
    'sphinx.ext.extlinks',
]

intersphinx_mapping = {
    'python': ('https://docs.python.org/3/', None),
    'sage': ('https://doc.sagemath.org/html/en/reference/', 'sage_objects.inv'),
}

# Useful shorthand roles from sage_package
extlinks = {
    'arxiv':     ('https://arxiv.org/abs/%s',         'arXiv:%s'),
    'wikipedia': ('https://en.wikipedia.org/wiki/%s', 'Wikipedia: %s'),
    'oeis':      ('https://oeis.org/%s',              'OEIS: %s'),
    'doi':       ('https://dx.doi.org/%s',            'doi:%s'),
}

templates_path = ['_templates']
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

#autodoc_default_options = {
#    'members': True,
#    'undoc-members': True,
#    'show-inheritance': True,
#    'imported-members': False,  # ← this is the key line
#}

autodoc_member_order = 'bysource'

# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_static_path = ['_static']
html_css_files = [
    'custom.css',
]

html_theme = 'furo'
# html_theme_path = [sage_package.sphinx.themes_path()]

# pygments_style = 'sphinx'
