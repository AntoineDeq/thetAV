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

from sage.categories.cartesian_product import cartesian_product
from sage.rings.polynomial.msolve import *
from copy import deepcopy as cop
from sage.matrix.all import Matrix, zero_matrix
from sage.rings.all import PolynomialRing, Integer, ZZ, Zmod
from random import choice, sample
from sage.structure.factory import *
from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
from sage.misc.functional import log
from sage.misc.misc_c import prod
from sage.all import EllipticCurve
# from sage.modules.free_module_element import vector, FreeModuleElement
# from sage.schemes.generic.morphism import SchemeMorphism_point
# from sage.structure.all import Sequence
# from sage.structure.element import AdditiveGroupElement
# from sage.structure.richcmp import richcmp_method, richcmp, op_EQ, op_NE

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
    """
    Check if L forms a basis of Zm ** (2 * g), where Zm is the base ring of the elements of L.
    
    TODO: can be optimized with pseudo_smith ? (echelon form not implemented over finite rings)
    """
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
    if fact_proj_l == 0 or fact_proj_r == 0:
        for i, j in cartesian_product([Z2n] * 2):
            if all(ZZ(e) % 2 == 0 for e in list(i + j)):
                ipj = Zn([ZZ(e) // 2 for e in list(i + j)])
                imj = Zn([ZZ(e) // 2 for e in list(i - j)])
                fact_proj_l = thet_n[ipj] * thet_n[imj]
                fact_proj_r = sum(thet_2n[i + t] * thet_2n[j + t] for t in Bp._twotorsion)
                if fact_proj_l != 0 and fact_proj_r != 0:
                    break
    for i, j in cartesian_product([Z2n] * 2):
        if all(ZZ(e) % 2 == 0 for e in list(i + j)):
            ipj = Zn([ZZ(e) // 2 for e in list(i + j)])
            imj = Zn([ZZ(e) // 2 for e in list(i - j)])
            if thet_n[ipj] * thet_n[imj] / fact_proj_l != sum(thet_2n[i + t] * thet_2n[j + t] for t in Bp._twotorsion) / fact_proj_r:
                return False
    return True

def new_rand_ab_var(g, m, n, FF11, FF):
    """
    Create a random abelian variety of genus g, level m, computed from a random curve,
    and a random basis of its n-torsion, with n such that n=md with d|m.
    FF11 is a field in which we choose the roots of the curve and FF the field of definition
    of the abelian variety, big enough to allow to compute all the n-torsion.
    """
    d = n // m
    assert(type(log(d, 2)) is Integer)

    B = sample(list(FF11), 2 * g + 1) # {branch points a_i} - \infty
    B.sort()
    B = [FF(e) for e in B]
    # print(B)

    ### Creation of the curve and computation of the corresponding abelian variety
    Q = PolynomialRing(FF, 'x')
    x, = Q.gens()
    
    p = prod([x - e for e in B])
    if g == 1:
        coeffs_p = list(p)
        coeffs_p.reverse()
        coeffs = [0] + coeffs_p[1:2] + [0] + coeffs_p[2:]
        E = EllipticCurve(FF, coeffs)
        # j_inv_E = E.j_invariant()
        if m == 2:
            Theta2 = utilities.Legendre_to_lv2tnp(utilities.Elliptic_to_Legendre(E)[0])[0]
            A = constructor.AbelianVariety(FF, m, g, Theta2)
        elif m == 4:
            Theta4 = utilities.generation_thet4(FF, B, g)
            A = constructor.AbelianVariety(FF, m, g, Theta4, check = True)
        else:
            raise NotImplementedError('Random example for m > 4')
    else:
        E = HyperellipticCurve(p)
        if g == 2:
            A = constructor.AbelianVariety.from_curve(E, m)
        else:
            raise NotImplementedError('Random example for g > 2')
    
    print("Curve used for this test :", E)
    print("\nAbelian variety used for this test :", A)

    bol = True
    cart_prod = cartesian_product([A._D] * 2)
    ln = len(A._D) ** 2
    while bol:
        Gtest_m = sample([cart_prod[i] for i in range(ln)], 2 * g)
        bol = not(gene2(Gtest_m))
    print("\nNumbering of the selected basis :", Gtest_m)
    Gtest_L = [A(0).action_theta(x) for x in Gtest_m]
    Gtest_list = [utilities.half(A, [g]) for g in Gtest_L]
    for _ in range(log(d, 2) - 1):
        Gtest_list = [utilities.half(A, g) for g in Gtest_list]
    print("\nA[n] computed")
    
    Gtest = [choice(e) for e in Gtest_list]

    return A, Gtest

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
    Q = PolynomialRing(FF, 'x')
    x, = Q.gens()
    
    p = prod([x - e for e in B])
    if g == 1:
        coeffs_p = list(p)
        coeffs_p.reverse()
        coeffs = [0] + coeffs_p[1:2] + [0] + coeffs_p[2:]
        E = EllipticCurve(FF, coeffs)
        # j_inv_E = E.j_invariant()
        if m == 2:
            Theta2 = utilities.Legendre_to_lv2tnp(utilities.Elliptic_to_Legendre(E)[0])[0]
            A = constructor.AbelianVariety(FF, m, g, Theta2)
        elif m == 4:
            Theta4 = utilities.generation_thet4(FF, B, g)
            A = constructor.AbelianVariety(FF, m, g, Theta4, check = True)
        else:
            raise NotImplementedError('Random example for m > 4')
    else:
        E = HyperellipticCurve(p)
        if g == 2:
            A = constructor.AbelianVariety.from_curve(E, m)
        else:
            raise NotImplementedError('Random example for g > 2')
    
    print("Curve used for this test :", E)
    print("\nAbelian variety used for this test :", A)
    
    if m == 2:
        print("\nTest not working for m = 2, debug as to be done for basic functions")
    ######
    
    lst_ai = choice(tools.set_sum_squares(d, n))
    
    bol = True
    cart_prod = cartesian_product([A._D] * 2)
    ln = len(A._D) ** 2
    while bol:
        Gtest_m = sample([cart_prod[i] for i in range(ln)], 2 * g)
        bol = not(gene2(Gtest_m))
    print("\nNumbering of the selected basis :", Gtest_m)
    Gtest_L = [A(0).action_theta(x) for x in Gtest_m]
    Gtest_list = [utilities.half(A, [g]) for g in Gtest_L]
    for _ in range(log(d, 2) - 1):
        Gtest_list = [utilities.half(A, g) for g in Gtest_list]
    print("\nA[n] computed")
    
    if supp is None:
        Gtest = [choice(e) for e in Gtest_list]
        
        try:
            Ap, _ = A.change_level(n, lst_ai, Gtest)
            
            print("\nNew abelian variety :", Ap)
            if d == 2:
                if verif_duplication_formula(A, Ap):
                    print("\nTest successful")
                else:
                    print("\nTest compiled but failed on duplication formulas")
            else:
                print("\nTest compiled with a valid theta null point, but compatibility has not been checked as d > 2")
        except ValueError as inst:
            if inst.args[0] == "The given list does not define a valid thetanullpoint":
                print("\nTest compiled but failed")
            else:
                print("\nTest failed", inst.args[0])
    
    else:
        nb_tests = 1
        for Gtest in cartesian_product(Gtest_list):
            try:
                Ap, _ = A.change_level(n, lst_ai, Gtest)
                if d == 2:
                    if verif_duplication_formula(A, Ap):
                        print("\nTest n°{} worked".format(nb_tests))
                    else:
                        print("\nTest n°{} compiled but failed".format(nb_tests))
                else:
                    print("\nTest n°{} compiled with a valid theta null point, but compatibility has not been checked as d > 2".format(nb_tests))
            except ValueError as inst:
                if inst.args[0] == "The given list does not define a valid thetanullpoint":
                    print("\nTest n°{} compiled but failed".format(nb_tests))
                else:
                    print("\nTest n°{} failed".format(nb_tests))
            nb_tests += 1
            if nb_tests >= supp:
                break

def gene_isog(Zmg2, ln, g, m, d):
    """
    Computes a random basis Gtest_m of a subgroup of A._D ** 2 isomorphic to A._D
    and a random basis Ktest_m of a subgroup of A[d] \cap <Gtest_m> isomorphic to Zm ** g.
    
    TODO: can be optimized with pseudo_smith ? (echelon form not implemented over finite rings)
    """
    Zm = Zmg2.base_ring()
    Zmg = Zm ** g
    a = None
    dico = {}
    bol = True
    while bol:
        Gtest_m = sample([Zmg2[i] for i in range(ln)], g) # [(A._D(1), A._D(0)), (A._D(0), A._D(1))]
        bol = tools.is_isotrop(Gtest_m)
        if bol:
            for f in Gtest_m:
                for b in Zmg2:
                    a = Matrix([b[0], b[1]])
                    a.set_immutable()
                    dico[a] = False
                usef = []
                for e in Zm:
                    b = Zmg2((e * f[0], e * f[1]))
                    a = Matrix([b[0], b[1]])
                    a.set_immutable()
                    dico[a] = True
                
                usef = [a for a, b in dico.items() if b]
                bol = bol and len(usef) == m
            
            for b in Zmg2:
                a = Matrix([b[0], b[1]])
                a.set_immutable()
                dico[a] = False
            usef = []
            for e in Zmg:
                comb_lin = [Zmg2((e[i] * Gtest_m[i][0], e[i] * Gtest_m[i][1])) for i in range(g)]
                b = Zmg2[0]
                for u in comb_lin:
                    b += u
                a = Matrix([b[0], b[1]])
                a.set_immutable()
                dico[a] = True
            
            usef = [Zmg2((Zmg(a[0,:][0]), Zmg(a[1,:][0]))) for a, b in dico.items() if b]
            bol = bol and len(usef) == m ** g
            # print("usef", usef)
        
        if bol:
            # print("G", Gtest_m)
            while bol:
                Ktest_m = sample(usef, g) # [ZZ(m / d) * e for e in Gtest_m] # attention, spécifique
                # print("K", Ktest_m)
                for f in Ktest_m:
                    for b in Zmg2:
                        a = Matrix([b[0], b[1]])
                        a.set_immutable()
                        dico[a] = False
                    for e in Zm:
                        b = Zmg2((e * f[0], e * f[1]))
                        a = Matrix([b[0], b[1]])
                        a.set_immutable()
                        dico[a] = True
                    usef2 = [a for a, b in dico.items() if b]
                    # print(f, usef2, len(usef2) == d, bol and len(usef2) == d)
                    bol = bol and len(usef2) == d
                
                for b in Zmg2:
                    a = Matrix([b[0], b[1]])
                    a.set_immutable()
                    dico[a] = False
                for e in Zmg:
                    comb_lin = [Zmg2((e[i] * Ktest_m[i][0], e[i] * Ktest_m[i][1])) for i in range(g)]
                    b = Zmg2[0]
                    for u in comb_lin:
                        b += u
                    a = Matrix([b[0], b[1]])
                    a.set_immutable()
                    dico[a] = True
                usef2 = [a for a, b in dico.items() if b]
                bol = bol and len(usef2) == d ** g
                bol = not(bol)
        else:
            bol = not(bol)
    return Gtest_m, Ktest_m

def test_isog_comput(g, m, n, FF11, FF, supp = None):
    """
    Test the isogeny computation for a random abelian variety, computed from a random curve,
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
    Q = PolynomialRing(FF, 'x')
    x, = Q.gens()
    
    p = prod([x - e for e in B])
    if g == 1:
        coeffs_p = list(p)
        coeffs_p.reverse()
        coeffs = [0] + coeffs_p[1:2] + [0] + coeffs_p[2:]
        E = EllipticCurve(FF, coeffs)
        # j_inv_E = E.j_invariant()
        if m == 2:
            Theta2 = utilities.Legendre_to_lv2tnp(utilities.Elliptic_to_Legendre(E)[0])[0]
            A = constructor.AbelianVariety(FF, m, g, Theta2)
        elif m == 4:
            Theta4 = utilities.generation_thet4(FF, B, g)
            A = constructor.AbelianVariety(FF, m, g, Theta4, check = True)
        else:
            raise NotImplementedError('Random example for m > 4')
    else:
        E = HyperellipticCurve(p)
        if g == 2:
            A = constructor.AbelianVariety.from_curve(E, m)
        else:
            raise NotImplementedError('Random example for g > 2')
    
    print("Curve used for this test :", E)
    print("\nAbelian variety used for this test :", A)
    
    if m == 2:
        print("\nTest not working for m = 2, debug as to be done for basic functions")
    ######
    
    lst_ai = choice(tools.set_sum_squares(d, n))
    
    Gtest_m, Ktest_m = gene_isog(cartesian_product([A._D] * 2), len(A._D) ** 2, g, m, d)
    
    print("\nNumbering of the selected basis for A[m] :", Gtest_m)
    print("\nNumbering of the selected basis for K :", Ktest_m)
    
    Ktest = [A(0).action_theta(x) for x in Ktest_m]
    Gtest_L = [A(0).action_theta(x) for x in Gtest_m]
    Gtest_list = [utilities.half(A, [g]) for g in Gtest_L]
    for _ in range(log(d, 2) - 1):
        Gtest_list = [utilities.half(A, g) for g in Gtest_list]
    print("\nA[n] partially computed")
    
    power_prim_roots = [A.roots(n) ** i for i in range(n)]
    Zn = Zmod(n)
    def log_W_pair_matrix(GG):
        M = zero_matrix(Zn, 2 * g)
        for i, e in enumerate(GG):
            for j, f in enumerate(GG):
                if i > j:
                    a = Zn(power_prim_roots.index(e.weil_pairing(f, n)))
                    M[i, j] = a
                    M[j, i] = -a
        return M
    
    if supp is None:
        Gtest = [choice(e) for e in Gtest_list]

        assert log_W_pair_matrix(Gtest) == zero_matrix(Zn, 2 * g)

        try:
            Ap, _ = A.isog_comput(n, lst_ai, Ktest, Gtest)
            
            print("\nNew abelian variety :", Ap)
            print("\nTest compiled with a valid theta null point, but compatibility has not been checked")
        except ValueError as inst:
            if inst.args[0] == "The given list does not define a valid thetanullpoint":
                print("\nTest compiled but failed")
            else:
                print("\nTest failed", inst.args[0])
    
    else:
        nb_tests = 1
        for Gtest in cartesian_product(Gtest_list):
            assert log_W_pair_matrix(Gtest) == zero_matrix(Zn, 2 * g)
            try:
                Ap, _ = A.isog_comput(n, lst_ai, Ktest, Gtest)
                print("\nTest n°{} compiled with a valid theta null point, but compatibility has not been checked".format(nb_tests))
            except ValueError as inst:
                if inst.args[0] == "The given list does not define a valid thetanullpoint":
                    print("\nTest n°{} compiled but failed".format(nb_tests))
                else:
                    print("\nTest n°{} failed".format(nb_tests))
            nb_tests += 1
            if nb_tests >= supp:
                break
