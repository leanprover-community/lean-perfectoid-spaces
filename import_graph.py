"""
Import graph generator. The resulting files can be opened in yEd. Then go to
Edit menu, properties mapper, add new configuration and then new entry, it will
understand you want your labels back. Then choose hierarchical layout.
"""
import os
from pathlib import Path

import regex
import networkx as nx

SRC_DIR = Path('src')
IMPORT_RE = regex.compile(r'^import (.*)')

def get_imports(path):
    """
    Return the list of files imported by the file at path
    """
    imports = []
    for line in path.read_text().split('\n'):
        m = IMPORT_RE.match(line)
        if m:
            # Hopefully remove comments and split multiple imports
            imports.extend(m.group(1).split('--')[0].strip().split())
    return imports

def get_name(path):
    """
    Build the Lean name of the file at path
    """
    return str(path.relative_to(SRC_DIR).with_suffix('')).replace(os.sep, '.')

fullG = nx.DiGraph()
G = nx.DiGraph()

# First collect files that belong to our repo
full_files = [get_name(path) for path in sorted(SRC_DIR.rglob('*.lean'))]
fullG.add_nodes_from(full_files)
for node in fullG.nodes():
    fullG.node[node]['label'] = node

# Same story excluding for_mathlib
files = [get_name(path) for path in sorted(SRC_DIR.rglob('*.lean'))
         if 'for_mathlib' not in path.parts]
G.add_nodes_from(files)
for node in G.nodes():
    G.node[node]['label'] = node

for path in sorted(SRC_DIR.rglob('*.lean')):
    cur_name = get_name(path)
    for filepath in get_imports(path):
        if filepath in full_files:
            fullG.add_edge(filepath, cur_name)
        if filepath in files:
            G.add_edge(filepath, cur_name)

nx.write_graphml(fullG, 'imports_full.graphml')
nx.write_graphml(G, 'imports.graphml')
