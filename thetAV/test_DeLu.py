"""
Tests for [DeLu25].

AUTHORS:

- Antoine Dequay 2025 initial implementation

"""

# *****************************************************************************
#       Copyright (C) 2025 Antoine Dequay <antoine.dequay@univ-rennes.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 3 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# *****************************************************************************

from functools import *
from itertools import *
from sage.rings.polynomial.msolve import *
from copy import deepcopy as cop
from sage.structure.coerce_maps import CallableConvertMap
from sage.structure.richcmp import richcmp_method, richcmp, op_EQ, op_NE
from sage.structure.element import is_Vector
from sage.schemes.generic.morphism import SchemeMorphism_point
from thetAV.tools import idx
from sage.misc.mrange import cantor_product
from sage.schemes.hyperelliptic_curves.invariants import clebsch_invariants, clebsch_to_igusa
from random import choice
import sys
integer_types = (int, Integer)

def progress_bar(count, total, prefix, size=50):
    full = '#'
    empty = '.'
    x = int(size * count / total)
    sys.stdout.write('\r' + prefix + ' ' + full*x + empty*(size-x) + ' ' + str(count).rjust(len(str(total)), ' ') + "/" + str(total))
    if count == total:
        sys.stdout.write('\n')


def gene2(L):
    g = len(L)
    Zm = L[0][0].base_ring()
    Zmg = Zm ** g
    D = L[0][0].parent()
    Zmg2 = cartesian_product([D] * 2)
    L = [Zmg2(e) for e in L]
    a = None
    dico = {}
    generators = [(e, D(0)) for e in D.gens()] + [(D(0), e) for e in D.gens()]
    for un in generators:
        b = cop(un)
        a = Matrix([b[0], b[1]])
        a.set_immutable()
        dico[a] = False
    for e in Zmg:
        comb_lin = [Zmg2((e[i] * L[i][0], e[i] * L[i][1])) for i in range(g)]
        b = Zmg2[0]
        for u in comb_lin:
            b += u
        a = Matrix([b[0], b[1]])
        a.set_immutable()
        if a in dico.keys():
            dico[a] = True
    return all(b for _, b in dico.items())

