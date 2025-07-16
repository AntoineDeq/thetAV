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
from random import choice, sample
import sys
integer_types = (int, Integer)

from . import constructor, tools, utilities

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

def verif_duplication_formula(B, Bp):
    """
    Verify all relations of the duplication formula form for z1 = z2 = 0
    """
    thet_n = B(0)
    Zn = B._D
    thet_2n = Bp(0)
    Z2n = Bp._D

    fact_proj_l = thet_n[0] ** 2
    fact_proj_r = sum(thet_2n[Z2n(t)] ** 2 for t in Bp._twotorsion)
    for i, j in cartesian_product([Z2n] * 2):
        if all(ZZ(e) % 2 == 0 for e in list(i + j)):
            ipj = Zn([ZZ(e) // 2 for e in list(i + j)])
            imj = Zn([ZZ(e) // 2 for e in list(i - j)])
            if thet_n[ipj] * thet_n[imj] / fact_proj_l != sum(thet_2n[i + t] * thet_2n[j + t] for t in Bp._twotorsion) / fact_proj_r:
                print(i,j)
                print(thet_n[ipj] * thet_n[imj] / fact_proj_l, sum(thet_2n[i + t] * thet_2n[j + t] for t in Bp._twotorsion) / fact_proj_r)
                return False
    return True

def test_change_level(g, m, n, FF11, FF, supp = None):
    """
    Test the change of level for a random abelian variety, computed from a random curve,
    given the genus g, the level m, the new level n such that n=md with d|m,
    FF11 a field in which we choose the roots of the curve, and FF the field of definition
    of the abelian variety, big enough to allow to compute all the n-torsion.
    
    supp is either None if we want a random basis for the n-torsion,
    or a positive integer if we want to test supp possible bases of the n-torsion.
    """
    d = n // m
    assert(type(log(d, 2)) is Integer)

    B = sample(list(FF11), 2 * g + 1) # {branch points a_i} - \infty
    B.sort()
    B = [FF(e) for e in B]
    # print(B)

    ### Creation of the curve and computation of the corresponding abelian variety
    Q.<x> = PolynomialRing(FF)
    
    p = prod([x - e for e in B])
    if g == 1:
        coeffs_p = list(p)
        coeffs_p.reverse()
        coeffs = [0] + coeffs_p[1:2] + [0] + coeffs_p[2:]
        E = EllipticCurve(FF, coeffs)
        # j_inv_E = E.j_invariant()
        if m == 2:
            Theta2 = Legendre_to_lv2tnp(Elliptic_to_Legendre(E)[0])[0]
            A = constructor.AbelianVariety(FF, m, g, Theta2)
        elif m == 4:
            Theta4 = generation_thet4(B, g)
            A = constructor.AbelianVariety(FF, m, g, Theta4, check = True)
        else:
            raise NotImplementedError('m > 4')
    else:
        E = HyperellipticCurve(p)
        if g == 2:
            A = AbelianVariety.from_curve(E, m)
        else:
            raise NotImplementedError('g > 2')
    
    print("Curve used for this test : ", E)
    print("\nAbelian variety used for this test : ", A)
    
    ######
    
    lst_ai = choice(tools.set_sum_squares(d, n))
    
    bol = True
    cart_prod = cartesian_product([A._D] * 2)
    ln = len(A._D) ** 2
    while bol:
        Gtest_m = sample([cart_prod[i] for i in range(ln)], 2 * g)
        bol = not(gene2(Gtest_m))
    print(Gtest_m)
    Gtest_L = [(A(0)).action_theta(x) for x in Gtest_m]
    Gtest_list = cop(Gtest_L)
    for _ in range(log(d, 2)):
        Gtest_list = [utilities.half(A, [g]) for g in Gtest_list]
    print("\nA[n] computed\n")
    
    if supp is None:
        Gtest = [choice(e) for e in Gtest_list]
        
        Ap, _ = A.change_level(n, lst_ai, Gtest)
        
        print("\nNew abelian variety : ", Ap)
        print("\nDuplication Formulas verified : ", verif_duplication_formula(A, Ap))
    
    else:
        nb_tests = 1
        for Gtest in cartesian_product(Gtest_list):
            try:
                Ap, _ = A.change_level(n, lst_ai, Gtest)
                if verif_duplication_formula(A, Ap):
                    print("Test n°{} worked".format(nb_tests))
                else:
                    print("Test n°{} compiled but failed".format(nb_tests))
            except:
                print("Test n°{} failed".format(nb_tests))
            nb_tests += 1
            if nb_tests >= supp:
                break
