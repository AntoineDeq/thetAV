"""
Additional tools.

AUTHORS:

- Antoine Dequay 2025 initial implementation

"""

# *****************************************************************************
#       Copyright (C) 2025 Antoine Dequay <antoine.dequay@ens-rennes.fr>
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
from . import tools
from sage.misc.mrange import cantor_product
from sage.schemes.hyperelliptic_curves.invariants import clebsch_invariants, clebsch_to_igusa
from random import choice
integer_types = (int, Integer)

def thet4(A, S):
    """
        Evaluate theta[n_S](0)^4 as in Mumford Tata II p. 120, up to a constant.

        INPUT:
            A is the list of branch points (without infty), with len(A) odd,
            S is a subset of the list of indices of A, with len(S) even.

        OUTPUT:

           theta[n_S](0)^4 up to a constant.
    """
    if len(S) % 2 == 1:
        raise ValueError(f"#S {S} odd, should be even")
    if len(A) % 2 == 0:
        raise ValueError(f"#A {A} even, should be odd")
    g = (len(A) - 1) // 2
    B = set(range(1, 2 * g + 2)) # indices of branch points
    U = set(range(1, 2 * g + 2, 2)) # indices of branch points of U
    SoU = S.symmetric_difference(U)
    SiU = S.intersection(U)
    BmSoU = B.difference(SoU)
    
    if len(SoU) != g + 1:
        return 0
    else:
        return (-1) ** len(SiU) * prod([(A[i - 1] - A[j - 1]) ** (-1) for i in SoU for j in BmSoU])

def mat_thomae(g, n = 4):
    """
    Change-of-basis matrix for the theta functions of level n, related to theta[n_S] as in Mumford Tata II p. 120 and [DeLu25].
    """
    Zn = Zmod(n) ** g
    Z2 = Zmod(2) ** g
    Z2n = [tools.from_m_to_n(Zn, z) for z in Z2]
    M = matrix.zero(FF, n ** g)
    for k in range(n ** g):
        ind = ZZ(k).digits(2, padto = 2 * g)
        chi = Z2(ind[:g])
        i = Zn(ind[g:])
        for t in Z2n:
            M[k, tools.idx(i + t, n)] = tools.eval_car(chi, t)
    return M

def calc_U_Thomae(g):
    """
    Compute all theta[n_S] (see Mumford Tata II)
    """
    L1 = [0] * g
    L2 = [0] * g
    all = {i for i in range(1, 2 * g + 2)}
    a = Matrix(Zmod(2), [L1, L2])
    a.set_immutable()
    dico = {a : set()} #See notations of Mumford Tata II
    for i in range(g):
        L1[i] = 1
        a = Matrix(Zmod(2), [L1, L2])
        a.set_immutable()
        dico[a] = all.symmetric_difference({2 * i + 1})
        L2[i] = 1
        a = Matrix(Zmod(2), [L1, L2])
        a.set_immutable()
        dico[a] = all.symmetric_difference({2 * i + 2})
        L1[i] = 0
    a = Matrix(Zmod(2), [L1, L2])
    a.set_immutable()
    dico[a] = all.symmetric_difference({2 * g + 1})
    
    new = list(dico.keys())
    keys = list(dico.keys())
    goal = 2 ** (2 * g)
    
    while len(dico) < goal:
        e = new.pop()
        for f in keys:
            b = e + f
            b.set_immutable()
            if b not in dico:
                dico[b] = dico[e].symmetric_difference(dico[f])
                new.append(b)
        keys = list(dico.keys())
    return dico

def generation_thet4(B, g):
    """
    from the roots of the equation of an hyperelliptic curve, compute the theta functions of level 4.
    
    
    """
    dico = calc_U_Thomae(g)
    
    l = None
    ThetaJ4 = []
    for k in range(2 ** (2 * g)):
        l = ZZ(k).digits(2, padto = 2 * g)
        l = Matrix([l[:g], l[g:]])
        l.set_immutable()
        ThetaJ4.append(FF(thet4(B, dico[l])))
    
    # Extraction of roots to be done properly (g = 2 in Cosset).
    
    ThetaJ2 = [sqrt(e) for e in ThetaJ4]
    ThetaJ = [sqrt(e) for e in ThetaJ2]
    Theta = list(mat_thomae(g).solve_right(Matrix(ThetaJ).transpose()).transpose()[0])
    return Theta

def groeb_roots(L, LX, sub, stop=Infinity):
    """
    Test all combinations of roots given by groebner_basis
    """
    if L == []:
        return [[]]
    if L[-1] == 0:
        return groeb_roots(L[:-1], LX, sub, stop)
    po = PolynomialRing(FF, LX[-1])(L[-1])
    for fact in po.factor():
        if fact[0].degree() > 1 and fact[0] != LX[-1] ** fact[0].degree():
            raise ValueError('Bad field, list of factors : ', po.factor())
    new_roots = po.roots(ring = FF, multiplicities = None)
    U = cop(L[:-1])
    new_sub = cop(sub)
    res = []
    for r in new_roots:
        new_sub[len(LX) - 1] = r
        for j in range(len(U)):
            U[j] = U[j](new_sub)
        part_res = groeb_roots(U, LX[:-1], new_sub)
        res = res + [pr + [r] for pr in part_res]
        if len(res) >= stop:
            break
        U = cop(L[:-1])
    return res

def half(A, Lst, stop=Infinity):
    """Compute the half of the given list of points.

    Args:
        A (AbelianVariety): The abelian variety.
        Lst (list): The list of points to be halved.
        stop (int, optional): The maximum number of points to return. Defaults to Infinity.

    Returns:
        list: The list of halved points.
    """
    FF = A.base_ring()
    n = A.level()
    g = A.dimension()
    ng = n ** g
    
    if g == 1:
        arg = n
        Q = PolynomialRing(FF, arg, 'X', order = "lex")
    else:
        arg = g * (n,)
        Q = PolynomialRing(FF, *arg, var_array='X', order = "lex")
    
    X = list(Q.gens())
    AA = AbelianVariety(Q, n, g, [Q(e) for e in tuple(A(0))])
    
    #Equations of the variety
    eqvar = [e(X) for e in A.equations()]
    
    #Equations for doubling
    eqmult = list(AA(X)._mult(2))
    
    List_Id = []
    for a in Lst:
        List_Id.append(Q.ideal([eqmult[i] - tuple(a)[i] for i in range(ng)] + eqvar))
    
    Lst_div = []
    for e in List_Id:
        Lst_div += groeb_roots(e.groebner_basis(), X, X, stop=stop)
    
    Lst_div = [A(e) for e in Lst_div]
    
    for i in range(ng):
        j = 0
        while j != len(Lst_div):
            if Lst_div[j][i] != 0:
                u = Lst_div[j][i]
                Lst_div[j] = tuple([Lst_div[j][k]/u for k in range(ng)])
                j += 1
            else:
                Lst_div[j] = tuple(Lst_div[j])
                j += 1
        Lst_div = list(set(Lst_div))
    
    Lst_div = [A(e) for e in Lst_div]
    
    return Lst_div

# Computation of the action of Sp_2g(Z/mZ) on the theta functions.

def Sg(Zm, g, C):
    return block_matrix([[identity_matrix(Zm, g), zero_matrix(Zm, g)], [C, identity_matrix(Zm, g)]])

def Bg(Zm, g, A):
    return block_matrix([[A, zero_matrix(Zm, g)], [zero_matrix(Zm, g), A.transpose().inverse()]])

def xgcd(a, b=None):
    """
    source : https://github.com/sagemath/sage/blob/develop/src/sage/arith/misc.py#L1939
    """
    if b is not None:
        # xgcd of two elements
        try:
            return a.xgcd(b)
        except AttributeError:
            a = py_scalar_to_element(a)
            b = py_scalar_to_element(b)
        except TypeError:
            b = py_scalar_to_element(b)
        return a.xgcd(b)

    # xgcd for several elements (possibly more than one)
    if len(a) == 0:
        return (ZZ(0),)
    a = Sequence(a, use_sage_types=True)
    res = [a.universe().zero()]
    for b in a:
        g, s, t = xgcd(res[0], b)
        res[0] = g
        for i in range(1, len(res)):
            res[i] *= s
        res.append(t)
    return tuple(res)

def pseudo_smith(M0):
    """
        For M in M_g(Z/mZ), compute U, V in M_g(Z/mZ) 
        such that UMV is of the form diag(X, ..., X, 0, ..., 0).
                                          {r times }
        Warning : We need U and V in GL_g(Z/mZ), but it is not always the case...
        
        INPUT:
            M0 a matrix in M_g(Z/mZ)

        OUTPUT:

        -  U, V, M such that U * M0 * V == M
        -  and e pseudo rank r of M.        

        EXAMPLES:

            sage: TODO
    """
    R = M0.base_ring()
    m = R.characteristic()
    M = cop(M0)
    g = M.nrows()
    U = identity_matrix(R, g)
    V = identity_matrix(R, g)
    end = g - 1
    
    row = 0
    while row < end:
        nonzero_rows = [i for i in range(row, g) if M[i, row] != 0]
            
        if nonzero_rows == []:
            M.swap_columns(row, end)
            V.swap_columns(row, end)
            end -= 1
            continue
        
        M.swap_rows(row, nonzero_rows[0])
        U.swap_rows(row, nonzero_rows[0])
        
        p = gcd([Integer(M[i, row]) for i in range(row, g) if M[i, row] != 0] + [Integer(M[row, i]) for i in range(row, g) if M[row, i] != 0])
        
        if p == 0:
            continue
        
        while p != gcd([Integer(M[i, row]) for i in range(row, g) if M[i, row] != 0]) or p != gcd([Integer(M[row, i]) for i in range(row, g) if M[row, i] != 0]) or p != M[row, row]:
            
            nonzero_rows = [i for i in range(row, g) if M[i, row] != 0]
            if not nonzero_rows:
                continue
            
            coeffs = [Integer(M[i, row]) for i in nonzero_rows]
            u_list = xgcd(coeffs)
            u_list = list(u_list)
            p = u_list[0]
            u_list = u_list[1:]

            if [i for i in range(row, g) if u_list[0] * M[row, i] != 0] == []:
                i = 1
                while [j for j in range(row, g) if u_list[i] * M[row, j] != 0] == []:
                    i += 1
                M.swap_rows(row, nonzero_rows[i])
                U.swap_rows(row, nonzero_rows[i])
                u_list[0], u_list[i] = u_list[i], u_list[0]
            
            new_row = sum(u * M[i, :] for u, i in zip(u_list, nonzero_rows))
            M[row, :] = new_row
            new_row = sum(u * U[i, :] for u, i in zip(u_list, nonzero_rows))
            U[row, :] = new_row
            
            nonzero_cols = [i for i in range(row, g) if M[row, i] != 0]
            if not nonzero_rows:
                continue
            
            coeffs = [Integer(M[row, i]) for i in nonzero_cols]
            u_list = xgcd(coeffs)
            u_list = list(u_list)
            p = u_list[0]
            u_list = u_list[1:]
            
            if [i for i in range(row, g) if u_list[0] * M[i, row] != 0] == []:
                i = 1
                while [j for j in range(row, g) if u_list[i] * M[j, row] != 0] == []:
                    i += 1
                M.swap_columns(row, nonzero_cols[i])
                V.swap_columns(row, nonzero_cols[i])
                u_list[0], u_list[i] = u_list[i], u_list[0]
            
            new_col = sum(u * M[:, i] for u, i in zip(u_list, nonzero_cols))
            M[:, row] = new_col
            new_col = sum(u * V[:, i] for u, i in zip(u_list, nonzero_cols))
            V[:, row] = new_col
            
            p = gcd([Integer(M[i, row]) for i in range(row, g) if M[i, row] != 0] + [Integer(M[row, i]) for i in range(row, g) if M[row, i] != 0])
        
        nonzero_rows = [i for i in range(row, g) if M[i, row] != 0]
        if not nonzero_rows:
            continue
        
        for i in range(g):
            if i != row and M[i, row] != 0:
                q = R(Integer(M[i, row]) / Integer(M[row, row]))
                M[i, :] -= q * M[row, :]
                U[i, :] -= q * U[row, :]

        for i in range(g):
            if i != row and M[row, i] != 0:
                q = R(Integer(M[row, i]) / Integer(M[row, row]))
                M[:, i] -= q * M[:, row]
                V[:, i] -= q * V[:, row]
        
        row += 1
    assert(U * M0 * V == M)
    # assert(U.det() != 0 and V.det() != 0)
    return M, U, V, len([i for i in range(g) if M[i, i] != 0])

def decomposition(M1, check = True):
    """
        Compute a decomposition of M in the basis B_g(A), S_g(C) and H_g.

        
        INPUT:
            M a matrix in Sp_{2g}(Z/mZ)

        OUTPUT:

        -  L a list of factors for M.
        

        EXAMPLES:

            sage: 
    """
    M = cop(M1)
    Zm = M.base_ring()
    g = M.nrows() // 2
    IDg = identity_matrix(Zm, g)
    mIDg = -IDg
    mID2g = -identity_matrix(Zm, 2 * g)
    Hg = block_matrix([[zero_matrix(Zm, g), IDg], [mIDg, zero_matrix(Zm, g)]])
    L_left = []
    L_right = []
    
    if not M[:g,:g].is_invertible():
        if M[g:,:g].is_invertible():
            L_left = L_left + [(("Bg", mIDg), mID2g), (("Hg", 1), Hg)]
            M = Hg * M
        else:
            _, U, V, r = pseudo_smith(M[g:,g:])
            L_left.append((("Bg", U.inverse()), Bg(Zm, g, U.inverse())))
            L_right.append((("Bg", V.inverse()), Bg(Zm, g, V.inverse())))
            M = Bg(Zm, g, U) * M * Bg(Zm, g, V)
            X = block_matrix([[zero_matrix(Zm, r), zero_matrix(Zm, r, g - r)], [zero_matrix(Zm, g - r, r), identity_matrix(Zm, g - r)]])
            L_left = L_left + [(("Bg", mIDg), mID2g), (("Hg", 1), Hg), (("Sg", X), Sg(Zm, g, X)), (("Hg", 1), Hg)]
            M = mID2g * Hg * Sg(Zm, g, -X) * Hg * M
    
    A = M[:g,:g]
    if A != identity_matrix(Zm, g):
        L_left.append((("Bg", A), Bg(Zm, g, A)))
        M = Bg(Zm, g, A.inverse()) * M
    
    C = M[g:,:g]
    if C != zero_matrix(Zm, g):
        L_left.append((("Sg", C), Sg(Zm, g, C)))
        M = Sg(Zm, g, -C) * M
    
    B = M[:g,g:]
    if B != zero_matrix(Zm, g):
        L_left = L_left + [(("Bg", mIDg), mID2g), (("Hg", 1), Hg), (("Sg", -B), Sg(Zm, g, -B)), (("Hg", 1), Hg)]
        M = mID2g * Hg * Sg(Zm, g, B) * Hg * M

    if check:
        assert(M != identity_matrix(Zm, 2 * g))
        assert(prod([e for (_, e) in L_left] + [e for (_, e) in L_right]) == M1)
    return L_left + L_right


def calc_sqr_Sg(C, check = True):
    """
        Compute \\sqrt(\\gamma_C(i)(i)) as described in [Prop 9].

        INPUT:
            C a symmetric matrix in M_g(Z/mZ)

        OUTPUT:

        -  dico a dictionary of the form i -> \\sqrt(\\gamma_C(i)(i))
        for i a (Matrix) vector of Zm**g.
        

        EXAMPLES:

            sage: 
    """
    g = C.nrows()
    Zm = C.base_ring()
    m = Zm.cardinality()
    Zmg = Zm ** g
    mg = len(Zmg)
    B = MatrixSpace(Zm, g, 1).basis().items()
    dico = {}
    new = []
    rac, a, items = None, None, None
    for _, vk in B:
        rac = sqrt(eval_car_comp(vector_to_Zmg(Zmg, C * vk), vector_to_Zmg(Zmg, vk), m))
        dico[vk] = rac
        new.append((vk, rac))
    if check:
        cond = new != []
    else:
        cond = len(dico) != mg
    while cond:
        i, raci = new.pop()
        items = list(dico.items())
        for j, racj in items:
            a = i + j
            a.set_immutable()
            if a not in dico:
                rac = raci * racj * eval_car_comp(vector_to_Zmg(Zmg, C * i), vector_to_Zmg(Zmg, j), m)
                dico[a] = rac
                new.append((a, rac))
            elif check:
                assert(dico[a] == raci * racj * eval_car_comp(vector_to_Zmg(Zmg, C * i), vector_to_Zmg(Zmg, j), m))
        if check:
            cond = new != []
        else:
            cond = len(dico) != mg
    return dico

