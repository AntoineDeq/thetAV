"""
Additional tools.

AUTHORS:

- Anna Somoza (2020-22): initial implementation
- Antoine Dequay (2025)

"""

# *****************************************************************************
#       Copyright (C) 2022 Anna Somoza <anna.somoza.henares@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 3 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
# *****************************************************************************

from itertools import combinations_with_replacement

from sage.rings.all import ZZ, Integer, Zmod
from sage.structure.coerce_maps import CallableConvertMap
from sage.misc.constant_function import ConstantFunction
from sage.misc.functional import sqrt
from sage.arith.misc import gcd
from sage.matrix.all import Matrix, block_matrix, zero_matrix, identity_matrix

integer_types = (int, Integer)


def rangeS(n, S):
    for x in range(n):
        if x in S:
            continue
        yield x


def reduce_sym(x):
    r"""
    Returns the lexicographic minimum among x and -x for x an element in
    Zmod(n)\ :sup:`g`.
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el = D([6, 6, 6, 3])
        sage: from thetAV.tools import reduce_sym
        sage: reduce_sym(el)
        (4, 4, 4, 7)
        
    """
    return min(x, -x)


def reduce_twotorsion(x):
    r"""
    Returns elements y in Zmod(2n)\ :sup:`g`, t in Zmod(2)\ :sup:`g` such that 
    x = y + t and y is the lexicographic minimum of the elements in the 
    class of x in Zmod(2n)\ :sup:`g` / Zmod(2)\ :sup:`g` with the usual 
    inclusion of Zmod(2) into Zmod(2n).
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el = D([9, 2, 0, 8])
        sage: from thetAV.tools import reduce_twotorsion
        sage: reduce_twotorsion(el)
        ((4, 2, 0, 3), (1, 0, 0, 1))

    """
    r = list(x)
    D = x.parent()
    n = D.rank()
    T = Zmod(2) ** n
    t = [0] * n
    halflevels = [i.order() // 2 for i in D.gens()]
    for i in range(n):
        if r[i] >= halflevels[i]:
            r[i] = r[i] - halflevels[i]
            t[i] = 1
    return D(r), T(t)


def reduce_symtwotorsion(x):
    r"""
    Returns elements y in Zmod(2n)\ :sup:`g`, t Zmod(2)\ :sup:`g` such that 
    y is the lexicographic minimum among the elements in the classes of 
    x and -x in Zmod(2n)\ :sup:`g` / Zmod(2)\ :sup:`g` with the usual 
    inclusion of Zmod(2) into Zmod(2n), and t is such that y + t is 
    either x or -x.
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el = D([8, 1, 5, 3])
        sage: from thetAV.tools import reduce_symtwotorsion
        sage: reduce_symtwotorsion(el)
        ((2, 4, 0, 2), (0, 1, 1, 1))
    
    """
    x1, tx1 = reduce_twotorsion(x)
    x2, tx2 = reduce_twotorsion(-x)
    return (x1, tx1) if x1 <= x2 else (x2, tx2)


def reduce_symcouple(x, y):
    r"""
    Returns the lexicographic minimum of the symmetrical reduction of two
    elements x, y in Zmod(n)\ :sup:`g`.
    
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el1 = D([4, 0, 5, 1]); el2 = D([9, 4, 6, 9])
        sage: from thetAV.tools import reduce_symcouple
        sage: reduce_symcouple(el1, el2)
        ((1, 6, 4, 1), (4, 0, 5, 1))
        
    """
    xred = reduce_sym(x)
    yred = reduce_sym(y)
    return (xred, yred) if xred < yred else (yred, xred)


def reduce_twotorsion_couple(x, y):
    r"""
    Given two elements x, y in Zmod(2n)\ :sup:`g`, returns elements r, s in
    Zmod(2n)\ :sup:`g`, t in Zmod(2)\ :sup:`g`, such that r is the lexicographic
    minimum among the elements in the classes of x and y in 
    Zmod(2n)\ :sup:`g` / Zmod(2)\ :sup:`g` with the usual  inclusion of Zmod(2)
    into Zmod(2n), s satisfies r + s = x + y and t is such that r + t is
    either x or y.
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el1 = D([8, 1, 8, 0]); el2 = D([5, 8, 4, 5])
        sage: from thetAV.tools import reduce_twotorsion_couple
        sage: reduce_twotorsion_couple(el1, el2)
        ((0, 3, 4, 0), (3, 6, 8, 5), (1, 1, 0, 1))
        
    """
    xred, tx = reduce_twotorsion(x)
    yred, ty = reduce_twotorsion(y)
    # check that the inclusion of Zmod(2)^g in Zmod(2n)^g is taken into account already.
    D = xred.parent()
    T = tx.parent()
    if not D.has_coerce_map_from(T):
        from sage.structure.coerce_maps import CallableConvertMap
        n = D.gens()[0].order()
        s = n // 2

        def c(P, el):
            return P(s * el.change_ring(ZZ))

        c = CallableConvertMap(T, D, c)
        D.register_coercion(c)
    return (xred, y + tx, tx) if xred < yred else (yred, x + ty,  ty)


def reduce_symtwotorsion_couple(x, y):
    r"""
    Given two elements x, y in Zmod(2n)\ :sup:`g`, returns elements r, s in
    Zmod(2n)\ :sup:`g`, t in Zmod(2)\ :sup:`g`, such that r is the lexicographic
    minimum among the elements in the classes of x, -x, y and -y in 
    Zmod(2n)\ :sup:`g` / Zmod(2)\ :sup:`g` with the usual  inclusion of Zmod(2)
    into Zmod(2n), s satisfies r + s = ± x ± y and t is such that r + t is
    either x, -x, y or -y.
    
    .. todo:: Is s minimal in any sense among all the ones that satisfy 
              that condition?
    
    EXAMPLES::
    
        sage: D = Zmod(10)^4
        sage: el1 = D([0, 7, 9, 1]); el2 = D([3, 5, 8, 8])
        sage: from thetAV.tools import reduce_symtwotorsion_couple
        sage: reduce_symtwotorsion_couple(el1, el2)
        ((0, 2, 4, 1), (3, 0, 3, 8), (0, 1, 1, 0))
        
    """
    xred, tx = reduce_symtwotorsion(x)
    yred, ty = reduce_symtwotorsion(y)
    # check that the inclusion of Zmod(2)^g in Zmod(2n)^g is taken into account already.
    D = xred.parent()
    T = tx.parent()
    if not D.has_coerce_map_from(T):
        from sage.structure.coerce_maps import CallableConvertMap
        n = D.gens()[0].order()
        s = n // 2

        def c(P, el):
            return P(s * el.change_ring(ZZ))

        c = CallableConvertMap(T, D, c)
        D.register_coercion(c)
    return (xred, reduce_sym(y + tx), tx) if xred < yred else (yred, reduce_sym(x + ty), ty)


def get_dual_quadruplet(x, y, u, v):
    """
    From a quadruplet well suited, compute a quadruplet such that the octuplet is in Riemann position
    """
    r = -x + y + u + v
    z = r.parent()([ZZ(e) // 2 for e in list(r)])
    xbis = x + z
    ybis = y - z
    ubis = u - z
    vbis = v - z
    return xbis, ybis, ubis, vbis


def eval_car(chi, t):
    """
    Evaluates the character chi at the element t, for elements in the 2-torsion
    """
    if chi.parent() != t.parent():
        r = list(t)
        D = t.parent()
        twotorsion = chi.parent()
        halflevels = [i.order() // 2 for i in D.gens()]
        n = D.rank()
        for i in range(n):
            r[i] = ZZ(r[i]) / halflevels[i]
        t = twotorsion(r)
    return ZZ(-1) ** (chi * t)

def evaluate_formal_points(w):
    r"""
    .. todo:: add minimal docstring.
    """
    B = w.parent()
    q = B.modulus()
    S = q.parent()
    u = S.gen()
    f = u * S(w.list()) * q.derivative()
    return f // q


def idx(c, n):
    """
    Return the integer index that corresponds to a given characteristic in ``D``.
    """
    return ZZ(list(c), n)


def create_conversions(n, g):
    r"""
    .. todo:: add minimal docstring.
    """
    Z = Zmod(n) ** g
    from_ZZ = CallableConvertMap(ZZ, Z, lambda U, idx: U(idx.digits(n, padto=g)))
    from_int = CallableConvertMap(int, Z, lambda U, idx: U(ZZ(idx).digits(n, padto=g)))
    from_int.domain = ConstantFunction(int)
    Z._unset_coercions_used()
    Z.register_conversion(from_ZZ)
    Z.register_conversion(from_int)
    return Z


def create_indexing(n, g, twotorsion=True):
    r"""
    .. todo:: add minimal docstring.
    """
    Z = create_conversions(n, g)
    if not twotorsion:
        return Z
    TT = create_conversions(2, g)
    if not Z.has_coerce_map_from(TT):
        s = n // 2
        c = CallableConvertMap(TT, Z, lambda U, tt: U([s * ZZ(i) for i in tt]))
        Z.register_coercion(c)
    return Z, TT

def from_m_to_n(Zn, tt):
    r"""
    .. todo:: add minimal docstring.
    """
    n = len(Zn.base_ring())
    m = len(tt.parent().base_ring())
    s = n // m
    return Zn([s * ZZ(i) for i in list(tt)])

def matrix_to_Zmg(Zmg, v):
    r"""
    .. todo:: add minimal docstring.
    """
    if v.nrows() != 1:
        v = v.transpose()
    if v.nrows() != 1:
        raise ValueError("Not a vector")
    return Zmg(tuple(v)[0])

def Zmg_to_matrix(v):
    r"""
    .. todo:: add minimal docstring.
    """
    return Matrix([list(v[0]) + list(v[1])]).T

def basis_num(G, n):
    """
        Return a possible numerotation of the basis of G in Z(n) compatible with the numerotation induced by the symplectic structure
    """
    m = G[0].scheme().level()
    g = G[0].scheme().dimension()
    d = n // m
    Zn = create_conversions(n, g)
    Zm = G[0].scheme()._D
    
    dG = [e.ell() for e in G]
    assert(all(e[0] == d for e in dG))
    assert(all(e[2][1] == Zm(0) for e in dG[:g]))
    assert(all(e[2][0] == Zm(0) for e in dG[g:]))

    return [Zn([ZZ(i) for i in list(tt[2][0])]) for tt in dG[:g]] + [Zn([ZZ(i) for i in list(tt[2][1])]) for tt in dG[g:]]

def basis_chain_basis(Zd, B0 = None):
    if B0 is None:
        B0 = list(Zd.gens())
    g = len(B0)
    B_chain = [B0[k] + B0[l] for k in range(g) for l in range(k + 1, g)]
    return B0, B_chain

def strat_decomp(Zd, B0 = None):
    B0, B_chain = basis_chain_basis(Zd, B0)
    res_en_cours = [Zd(0)] + B0 + B_chain
    pile_en_cours = B0 + B_chain
    ln_but = len(Zd)
    res = []
    bol = True
    while len(res_en_cours) != ln_but and bol:
        bol = False
        while len(res_en_cours) != ln_but and len(pile_en_cours) > 0: # Programming that favors diff_add
            e = pile_en_cours.pop()
            for f in res_en_cours:
                if e + f not in res_en_cours and e - f in res_en_cours:
                    res.append((2, e + f, e, f, e - f))
                    res_en_cours.append(e + f)
                    pile_en_cours.append(e + f)
                    bol = True
        if len(res_en_cours) == ln_but:
            break
        for e, f, g in combinations_with_replacement(res_en_cours, 3):
            if e + f + g not in res_en_cours and e + f in res_en_cours and e + g in res_en_cours and f + g in res_en_cours:
                res.append((3, e + f + g, e, f, g, e + f, f + g, e + g))
                res_en_cours.append(e + f + g)
                pile_en_cours.append(e + f + g)
                bol = True
    if len(res_en_cours) != ln_but:
        raise ValueError("can't compute everything")
    return res

def set_sum_squares(d, n, L = [], S = [], res = [], b = 0):
    if b == 0:
        L = [i ** 2 for i in range(1, d + 1) if i**2 <= d and gcd(i, n) == 1]
        S = [[u, [u]] for u in L]
        return set_sum_squares(d, n, L, S, [], 1)
    if b == d + 1:
        return [[sqrt(f) for f in e] for e in res]
    Sp = []
    res = res + [e[1] for e in S if e[0] == d]
    for e in S:
        for f in L:
            if f >= e[1][-1] and e[0] + f <= d:
                Sp.append([e[0] + f, e[1] + [f]])
    return set_sum_squares(d, n, L, Sp, res, b + 1)

def is_isotrop(basis):
    """
    Check if basis is isotropic
    """
    g = len(basis)
    Zn = basis[0][0].base_ring()
    J = block_matrix(Zn, [[zero_matrix(Zn, g), identity_matrix(Zn, g)], [-identity_matrix(Zn, g), zero_matrix(Zn, g)]])
    for e in basis:
        for f in basis:
            if (Zmg_to_matrix(e).T * J * Zmg_to_matrix(f)) != 0:
                return False
    return True

def M_vers_symplec(K, n):
    """
    Retourne une matrice symplectique M telle que M envoie les vecteurs de K
    sur les vecteurs e_1,...,e_g
    """
    Zn = Zmod(n)
    g = len(K)
    V = Zn ** (2 * g)
    J = block_matrix(Zn, [[zero_matrix(Zn, g), identity_matrix(Zn, g)], [-identity_matrix(Zn, g), zero_matrix(Zn, g)]])
    
    if not is_isotrop(K):
        raise ValueError("K is not isotropic.")
    
    basis = [Zmg_to_matrix(e) for e in K]
    for i in range(g, 2 * g):
        for candidate in V: # peut faire mieux ?
            cand = Matrix(Zn, [list(candidate)]).T
            if all((basis[j].T * J * cand) == 0 for j in range(i - g + 1, i)) and all((basis[j].T * J * cand) == 0 for j in range(i - g)) and (basis[i - g].T * J * cand) == 1:
                basis.append(cand)
                break
        else:
            raise ValueError("Impossible to extend the basis to a symplectic basis.")
    
    M = Matrix(Zn, [e.T[0] for e in basis]).T.inverse()
    assert M.T * J * M == J
    return M
