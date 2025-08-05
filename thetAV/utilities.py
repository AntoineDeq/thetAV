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

from itertools import combinations_with_replacement
from sage.rings.polynomial.msolve import *
from copy import deepcopy as cop
from sage.rings.infinity import *
from sage.matrix.all import Matrix, zero_matrix, identity_matrix, block_matrix, MatrixSpace
from sage.rings.all import PolynomialRing, Integer, ZZ, Zmod
from sage.schemes.hyperelliptic_curves.invariants import clebsch_invariants, clebsch_to_igusa
from sage.misc.misc_c import prod
from sage.structure.factory import *
from sage.all import EllipticCurve
from sage.misc.functional import sqrt
from sage.categories.cartesian_product import cartesian_product
from sage.arith.misc import gcd

from . import tools
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
    M = zero_matrix(n ** g)
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

def generation_thet4(FF, B, g):
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

def groeb_roots(FF, L, LX, sub, stop=Infinity):
    """
    Test all combinations of roots given by groebner_basis
    """
    if L == []:
        return [[]]
    if L[-1] == 0:
        return groeb_roots(FF, L[:-1], LX, sub, stop)
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
        part_res = groeb_roots(FF, U, LX[:-1], new_sub)
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
    AA = A.change_ring(Q)
    
    # Equations of the variety
    eqvar = [e(X) for e in A.equations()]
    
    # Equations for doubling
    # eqmult = list((AA(X))._mult(2))
    eqmult = list((AA(X)).diff_add(AA(X), AA(0)))
    
    List_Id = []
    for a in Lst:
        List_Id.append(Q.ideal([eqmult[i] - tuple(a)[i] for i in range(ng)] + eqvar))
    
    Lst_div = []
    for e in List_Id:
        Lst_div += groeb_roots(FF, e.groebner_basis(), X, X, stop=stop)
    
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

# *****************************************************************************
# Computation of the action of Sp_2g(Z/mZ) on the theta functions.
# *****************************************************************************


def Sg(Zm, g, C):
    r"""
    .. todo:: add minimal docstring.
    """
    return block_matrix([[identity_matrix(Zm, g), zero_matrix(Zm, g)], [C, identity_matrix(Zm, g)]])

def Bg(Zm, g, A):
    r"""
    .. todo:: add minimal docstring.
    """
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
                                          {i times }
        Warning : We need U and V in GL_g(Z/mZ), but it is not always the case...
        
        INPUT:
            M0 a matrix in M_g(Z/mZ)

        OUTPUT:

        -  U, V, M such that U * M0 * V == M
        -  i the pseudo rank of M.

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
    
    i, j = 0, g - 1
    while i < j:
        if gcd(ZZ(M[i, i]), m) == 1:
            i += 1
            if gcd(ZZ(M[j, j]), m) != 1:
                j -= 1
        else:
            if gcd(ZZ(M[j, j]), m) == 1:
                M.swap_columns(i, j)
                V.swap_columns(i, j)
                M.swap_rows(i, j)
                U.swap_rows(i, j)
                i += 1
                j -= 1
            else:
                j -= 1
    assert(U * M0 * V == M)
    assert(U.is_invertible() and V.is_invertible())
    # print(M)
    return M, U, V, i

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
            _, U, V, r = pseudo_smith(M[:g,:g])
            # print(U, V, r)
            L_left.append((("Bg", U.inverse()), Bg(Zm, g, U.inverse())))
            L_right.append((("Bg", V.inverse()), Bg(Zm, g, V.inverse())))
            M = Bg(Zm, g, U) * M * Bg(Zm, g, V)
            # print(M)
            # print("\n")
            X = block_matrix([[zero_matrix(Zm, r), zero_matrix(Zm, r, g - r)], [zero_matrix(Zm, g - r, r), identity_matrix(Zm, g - r)]])
            L_left = L_left + [(("Bg", mIDg), mID2g), (("Hg", 1), Hg), (("Sg", X), Sg(Zm, g, X)), (("Hg", 1), Hg)]
            M = mID2g * Hg * Sg(Zm, g, -X) * Hg * M
            # print(M)
    
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
        assert(M == identity_matrix(Zm, 2 * g))
        assert(prod([e for (_, e) in L_left] + [e for (_, e) in L_right]) == M1)
    return L_left + L_right


def calc_sqr_Sg(A, C, check = True):
    """
        Compute \\sqrt(\\gamma_C(i)(i)) as described in [Prop 9].

        INPUT:
            C a symmetric matrix in M_g(Z/mZ)
            A the abelian variety

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
        rac = sqrt(A.eval_car_comp(tools.matrix_to_Zmg(Zmg, C * vk), tools.matrix_to_Zmg(Zmg, vk))) # a choice is made here
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
                rac = raci * racj * A.eval_car_comp(tools.matrix_to_Zmg(Zmg, C * i), tools.matrix_to_Zmg(Zmg, j))
                dico[a] = rac
                new.append((a, rac))
            elif check:
                assert(dico[a] == raci * racj * A.eval_car_comp(tools.matrix_to_Zmg(Zmg, C * i), tools.matrix_to_Zmg(Zmg, j)))
        if check:
            cond = new != []
        else:
            cond = len(dico) != mg
    return dico

# *****************************************************************************
# 
# *****************************************************************************

def Legendre_to_Elliptic(lm):
    """ 
    For given lm, compute E:y^2=x*(x-1)*(x-lm).
    """
    E = EllipticCurve(parent(lm), [0, (-lm - 1), 0, lm, 0])
    return E

def Elliptic_to_Legendre(E):
    """ 
    For given E, compute lmd s.t. y^2=x*(x-1)*(x-lmd).
    this form is called "Legendre form".
    """
    coeff = E.a_invariants()
    #y^2=x^3+ax^2+bx+c
    a = coeff[1]
    b = coeff[3]
    c = coeff[4]
    fld = E.base_field()
    X = gen(fld['X'])
    f = X ** 3 + a * X ** 2 + b * X + c
    roots = f.roots()
    # assert(len(roots) == 3)
    x1 = roots[0][0]
    x2 = roots[1][0]
    x3 = roots[2][0]
    lmd = (x3 - x1) / (x2 - x1)
    E_lmd = Legendre_to_Elliptic(lmd)
    iso_E_Elmd = E.isomorphisms(E_lmd)[1] # not 0 because trivial
    return lmd, E_lmd, iso_E_Elmd

def Legendre_to_lv2tnp(lm):
    """ 
    From Legendre form, compute theta-null point of level 2.
    """
    K = parent(lm)
    sq_rt_lm = sqrt(lm)
    sq_rt_lmm1 = sqrt(lm-1)
    # assert(sq_rt_lm ** 2 == lm)
    # assert(sq_rt_lmm1 ** 2 == lm - 1)
    thnp0_sq = sq_rt_lm
    thnp1_sq = sq_rt_lmm1
    thnp2_sq = K(1)
    lv2tnp = [(thnp0_sq + thnp2_sq), thnp1_sq]
    return lv2tnp, sq_rt_lm, sq_rt_lmm1

def Lv2tnp_to_Legendre(lv2tnp:list):
    """ 
    From theta-null point of level 2, compute Legendre form.
    """
    assert(len(lv2tnp) == 2)
    a = lv2tnp[0]
    b = lv2tnp[1]
    sq_rt_lm = (a ** 2 + b ** 2) / (a ** 2 - b ** 2)
    sq_rt_lmm1 = (1 + sq_rt_lm) * (lv2tnp[1] / lv2tnp[0])
    lm = sq_rt_lm ** 2
    assert(sq_rt_lmm1 ** 2 + 1 == lm)
    return lm, sq_rt_lm, sq_rt_lmm1

def Is_isomorphic_Legendre(lmd_1,lmd_2):
    """ 
    for 2 lmd, check if the defining elliptic curves are isomorphic.
    """
    if lmd_1 in {lmd_2, 1 / lmd_2, 1 - lmd_2, 1 / (1 - lmd_2), 1 - (1 / lmd_2), lmd_2 / (lmd_2 - 1)}:
        return True
    else:
        return False

def lv2tnp_to_j_inv(lv2tnp):
    """
    From theta-null point of level 2, compute the j-invariant of the assiociated elliptic curve.
    """
    B = lv2tnp.scheme()
    assert(B.dimension() == 1)
    assert(B.level() == 2)
    a = lv2tnp[0]
    b = lv2tnp[1]
    sq_rt_lm = (a ** 2 + b ** 2) / (a ** 2 - b ** 2)
    lm = sq_rt_lm ** 2
    j = 2 ** 8 * (lm ** 2 - lm + 1) ** 3 / (lm ** 2 * (lm - 1) ** 2)
    return j

def set_to_eta(S, g):
    """
    Compute eta_S as in Mumford [Tata II]
    """
    L1 = [0] * g
    L2 = [0] * g
    a = Matrix(Zmod(2), [L1, L2])
    for i in S:
        n = (i + 1) // 2
        L1 = [0] * (n - 1) + [1] + [0] * (g - n)
        if i % 2 == 0:
            L2 = [1] * n + [0] * (g - n)
        else:
            L2 = [1] * (n - 1) + [0] * (g - n + 1)
        if i == 0:
            L1 = [0] * g
            L2 = [0] * g
        if i == 2 * g + 1:
            L1 = [0] * g
            L2 = [1] * g
        a = a + Matrix(Zmod(2), [L1, L2])
    a.set_immutable()
    return a

def compute_formula_inv_thomae(thet, k, i, j, g):
    """
    Compute (ak - aj) / (ak - ai) as in [Cosset, Thm 3.1.20]. See def p.41 for syst. of representation

    Test every V possible (the first one should always be ok (?)
    """
    V = set([i, j])
    U = set(range(1, 2 * g + 2, 2)) # indices of branch points of U
    u = 0
    V_poss = [set(e) for e in combinations_with_replacement([f for f in range(1, 2 * g + 2) if f != k], 2) if len(set(e)) == g - 1]
    if V_poss == []:
        V_poss = [set()]
    ln = len(V_poss)
    while u != ln:
        V = V_poss[u].union(set([i, j]))
        
        UVi = set_to_eta(U.symmetric_difference(V).symmetric_difference(set([i])), g)
        UVi = [ZZ(e) for e in UVi[0, :][0]] + [ZZ(e) for e in UVi[1, :][0]]
        UVj = set_to_eta(U.symmetric_difference(V).symmetric_difference(set([j])), g)
        UVj = [ZZ(e) for e in UVj[0, :][0]] + [ZZ(e) for e in UVj[1, :][0]]
        UVik = set_to_eta(U.symmetric_difference(V).symmetric_difference(set([i, k])), g)
        UVik = [ZZ(e) for e in UVik[0, :][0]] + [ZZ(e) for e in UVik[1, :][0]]
        UVjk = set_to_eta(U.symmetric_difference(V).symmetric_difference(set([j, k])), g)
        UVjk = [ZZ(e) for e in UVjk[0, :][0]] + [ZZ(e) for e in UVjk[1, :][0]]
        
        etakp = set_to_eta(set([k]), g)[0, :]
        etaijpp = set_to_eta(set([i, j]), g)[1, :]
        
        if (thet[ZZ(UVi, 2)] ** 2 * thet[ZZ(UVjk, 2)] ** 2) != 0:
            return (-1) ** (etakp * etaijpp.transpose())[0, 0] * (thet[ZZ(UVj, 2)] ** 2 * thet[ZZ(UVik, 2)] ** 2) / (thet[ZZ(UVi, 2)] ** 2 * thet[ZZ(UVjk, 2)] ** 2)
        u += 1
    return None

def mat_inv_thomae(thet, g):
    """
    Compute M such that Ker(M) is the {a_i} as in inverse Thomae formula in [Cosset, Thm 3.1.20]
    """
    M = []
    L0 = [0] * (2 * g + 1)
    L_nouv = None
    for k, i, j in cartesian_product([range(2 * g + 1)] * 3):
        if len(set([k, i, j])) == 3:
            u = compute_formula_inv_thomae(thet, k + 1, i + 1, j + 1, g)
            if u is not None:
                L_nouv = cop(L0)
                L_nouv[k] = 1 - u
                L_nouv[i] = u
                L_nouv[j] = -1
                M.append(L_nouv)
    return Matrix(M)

def thet_us_to_thet_eta(tnp, n = 4):
    """
    level 4 ok, TODO: test for other levels
    """
    g = tnp.scheme().dimension()
    FF = tnp.scheme().base_ring()
    return list(mat_thomae(g, n).inverse().solve_right(Matrix(tnp).transpose()).transpose()[0])

def lv4tnp_to_ai_space(tnp):
    """
    Compute the sapce of solution for the ai's considering Thomae inverse formulas
    """
    g = tnp.scheme().dimension()
    thet = thet_us_to_thet_eta(tnp)
    M = mat_inv_thomae(thet, g)
    K = M.right_kernel()
    return K

def lv4tnp_to_j_inv(lv4tnp):
    """
    From theta-null point of level 4, compute the j-invariant of the assiociated elliptic curve.

    -> We compute the Legendre form for that, i.e. E:y^2=x*(x-1)*(x-lm)
    """
    B = lv4tnp.scheme()
    assert(B.dimension() == 1)
    assert(B.level() == 4)
    th = [0] * 16
    
    K = lv4tnp_to_ai_space(lv4tnp)
    Basis = K.basis()
    M = Matrix([[e[i] for e in Basis] for i in range(2)])
    goal = Matrix([[0, 1]]).transpose()
    pre_res = M.solve_right(goal)
    
    lm = (Matrix([e[2] for e in Basis]) * pre_res)[0,0]
    E = EllipticCurve(parent(lm), [0, (-lm - 1), 0, lm, 0])
    
    j = 2 ** 8 * (lm ** 2 - lm + 1) ** 3 / (lm ** 2 * (lm - 1) ** 2)
    return j

def equation_to_igusa_inv(p): # coherent with lv4tnp_to_igusa_inv
    r"""
    .. todo:: add minimal docstring.
    """
    A, B, C, D = clebsch_invariants(p)
    I2, I4, I6, I10 = clebsch_to_igusa(A, B, C, D)
    j1, j2, j3 = I2 ** 5 / I10, I4 * I2 ** 3 / I10, I6 * I2 ** 2 / I10 # see version j' of Weng [Wen01] p.28, PHD thesis in German
    return j1, j2, j3

def lv4tnp_to_igusa_inv(lv4tnp): # cohérent with equation_to_igusa_inv
    """
    From theta-null point of level 4, compute the Igusa invariants of the assiociated hyperelliptic curve.

    See formulas from [DupontPhd] -> def 5.2, section 6.2, section 6.3.3
    """
    B = lv4tnp.scheme()
    assert(B.dimension() == 2)
    assert(B.level() == 4)
    g = B.dimension()
    #θb0+2b1+4a0+8a1 = θa,b -> inverse % the rest of this module
    th = [0] * 16
    
    def trad(k): # b and a have inverse role in formulas compared to the rest of this module
        l = ZZ(k).digits(2, padto = 2 * g)
        return ZZ(l[g:] + l[:g], 2)
    
    thet = thet_us_to_thet_eta(lv4tnp, g)
    for k in range(16):
        th[trad(k)] = thet[k]
    
    P2 = {0, 1, 2, 3, 4, 6, 8, 9, 12, 15}
    h4 = sum([th[j] ** 8 for j in P2])
    h10 = prod([th[j] ** 2 for j in P2])
    h12 = (th[0] * th[1] * th[2] * th[4] * th[8] * th[15]) ** 4 + (th[0] * th[1] * th[2] * th[6] * th[9] * th[12]) ** 4 + (th[0] * th[1] * th[3] * th[4] * th[9] * th[15]) ** 4 + (th[0] * th[1] * th[3] * th[6] * th[8] * th[12]) ** 4 + (th[0] * th[1] * th[4] * th[6] * th[12] * th[15]) ** 4 + (th[0] * th[2] * th[3] * th[4] * th[9] * th[12]) ** 4 + (th[0] * th[2] * th[3] * th[6] * th[8] * th[15]) ** 4 + (th[0] * th[2] * th[8] * th[9] * th[12] * th[15]) ** 4 + (th[0] * th[3] * th[4] * th[6] * th[8] * th[9]) ** 4 + (th[1] * th[2] * th[3] * th[4] * th[8] * th[12]) ** 4 + (th[1] * th[2] * th[3] * th[6] * th[9] * th[15]) ** 4 + (th[1] * th[2] * th[4] * th[6] * th[8] * th[9]) ** 4 + (th[1] * th[3] * th[8] * th[9] * th[12] * th[15]) ** 4 + (th[2] * th[3] * th[4] * th[6] * th[12] * th[15]) ** 4 + (th[4] * th[6] * th[8] * th[9] * th[12] * th[15]) ** 4
    h16 = (th[3] ** 8 + th[6] ** 8 + th[9] ** 8 + th[12] ** 8) * (th[0] * th[1] * th[2] * th[4] * th[8] * th[15]) ** 4 + (th[3] ** 8 + th[4] ** 8 + th[8] ** 8 + th[15] ** 8) * (th[0] * th[1] * th[2] * th[6] * th[9] * th[12]) ** 4 + (th[2] ** 8 + th[6] ** 8 + th[8] ** 8 + th[12] ** 8) * (th[0] * th[1] * th[3] * th[4] * th[9] * th[15]) ** 4 + (th[2] ** 8 + th[4] ** 8 + th[9] ** 8 + th[15] ** 8) * (th[0] * th[1] * th[3] * th[6] * th[8] * th[12]) ** 4 + (th[2] ** 8 + th[3] ** 8 + th[8] ** 8 + th[9] ** 8) * (th[0] * th[1] * th[4] * th[6] * th[12] * th[15]) ** 4 + (th[1] ** 8 + th[6] ** 8 + th[8] ** 8 + th[15] ** 8) * (th[0] * th[2] * th[3] * th[4] * th[9] * th[12]) ** 4 + (th[1] ** 8 + th[4] ** 8 + th[9] ** 8 + th[12] ** 8) * (th[0] * th[2] * th[3] * th[6] * th[8] * th[15]) ** 4 + (th[1] ** 8 + th[3] ** 8 + th[4] ** 8 + th[6] ** 8) * (th[0] * th[2] * th[8] * th[9] * th[12] * th[15]) ** 4 + (th[1] ** 8 + th[2] ** 8 + th[12] ** 8 + th[15] ** 8) * (th[0] * th[3] * th[4] * th[6] * th[8] * th[9]) ** 4 + (th[0] ** 8 + th[6] ** 8 + th[9] ** 8 + th[15] ** 8) * (th[1] * th[2] * th[3] * th[4] * th[8] * th[12]) ** 4 + (th[0] ** 8 + th[4] ** 8 + th[8] ** 8 + th[12] ** 8) * (th[1] * th[2] * th[3] * th[6] * th[9] * th[15]) ** 4 + (th[0] ** 8 + th[3] ** 8 + th[12] ** 8 + th[15] ** 8) * (th[1] * th[2] * th[4] * th[6] * th[8] * th[9]) ** 4 + (th[0] ** 8 + th[2] ** 8 + th[4] ** 8 + th[6] ** 8) * (th[1] * th[3] * th[8] * th[9] * th[12] * th[15]) ** 4 + (th[0] ** 8 + th[1] ** 8 + th[8] ** 8 + th[9] ** 8) * (th[2] * th[3] * th[4] * th[6] * th[12] * th[15]) ** 4 + (th[0] ** 8 + th[1] ** 8 + th[2] ** 8 + th[3] ** 8) * (th[4] * th[6] * th[8] * th[9] * th[12] * th[15]) ** 4
    j1 = h12 ** 5 / h10 ** 6
    j2 = h4 * h12 ** 3 / h10 ** 4
    j3 = h16 * h12 ** 2 / h10 ** 4
    return j1, j2, j3