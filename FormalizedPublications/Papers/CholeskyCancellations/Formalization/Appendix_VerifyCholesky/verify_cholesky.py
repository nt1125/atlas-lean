#!/usr/bin/env python3
"""
verify_cholesky.py -- independent verification of the two counterexamples in
"Accidental Cancellations in Cholesky Factorization"  (Nam Trang).

Part A (Theorem 5.1).  The 4x4 matrix

        A* = [[ 4, -2, -2, -1],
              [-2,  4,  1,  2],
              [-2,  1,  4,  2],
              [-1,  2,  2,  4]]

is SPD with spectrum {9,3,3,1} and pattern graph K_4.  None of its 24
elimination orderings has a cancellation-free FIRST Schur complement, so the
First-Schur Conjecture (Conjecture 2) is false; but 8 of the 24 orderings give
a clean Cholesky factor, so A* is NOT a counterexample to the Fill-Graph
Conjecture (Conjecture 1).  The gap between the two is the refill phenomenon.

Part B (Theorem 5.5).  With B = 1/2 and A = (-3 + sqrt(73))/8, the positive
root of the curve A^2 + (1 - B^2) A - 1 = 0, the 6x6 matrix

        M_6 = I_6 + AB*P + A*Q + B*R,
        P = I_3 (x) [[0,1],[1,0]],
        Q = (J_3 - I_3) (x) I_2,
        R = (J_3 - I_3) (x) [[0,1],[1,0]]

(vertices paired {0,1},{2,3},{4,5}; within-pair entry AB; each cross-pair block
[[A,B],[B,A]]) is SPD with pattern K_6, and NONE of its 720 orderings is clean.
That refutes the Fill-Graph Conjecture (Conjecture 1) at order 6, the smallest
order at which it fails.  Part B also re-checks the steps of the proof, not
just its conclusion: the forced zero matching after the first pivot, the forced
second pivot, and the covering of all survivors after it.

DEPENDENCIES: none.  Python standard library only (fractions, itertools, sys);
no NumPy, no SymPy, nothing to install.  Works on Python 3.7+.

ARITHMETIC: everything is exact.  Part A needs only rationals; Part B needs the
quadratic field Q(sqrt(73)), since A is irrational.  Both are handled by one
class Q: a number is a pair of Fractions standing for a + b*sqrt(73), with
exact equality, exact division, and an exact sign test that compares a^2 with
73*b^2 instead of evaluating a square root.  No decision anywhere in this
script is taken in floating point; floats appear only in printed decimals.
This matters: the claims are that certain entries are EXACTLY zero while their
neighbours are not, which no float computation can certify.

USAGE
    python3 verify_cholesky.py                 # both parts (about 1 second)
    python3 verify_cholesky.py --only astar    # Part A only
    python3 verify_cholesky.py --only m6       # Part B only
    python3 verify_cholesky.py --all           # + every stage of all 24
                                               #   orderings of A*
    python3 verify_cholesky.py --show-stages   # + the forced opening of M_6
    python3 verify_cholesky.py --m8            # + all 40320 orderings of M_8
                                               #   (about 40 seconds)
    python3 verify_cholesky.py --help

Exit status 0 if every check passes, 1 otherwise.
"""

import sys
from fractions import Fraction as F
from itertools import permutations

if "--help" in sys.argv or "-h" in sys.argv:
    print(__doc__)
    sys.exit(0)

D = 73                      # the quadratic field is Q(sqrt(D))
_ok = [True]
_count = [0]


def check(cond, msg):
    _count[0] += 1
    print(("  [ok]   " if cond else "  [FAIL] ") + msg)
    if not cond:
        _ok[0] = False


# --------------------------------------------------------------------------
# Exact arithmetic in Q(sqrt(D)); rationals are the b == 0 case.
# --------------------------------------------------------------------------

class Q(object):
    """a + b*sqrt(D) with a, b rational.  Exact."""
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a = F(a)
        self.b = F(b)

    def __add__(s, o):
        o = _q(o)
        return Q(s.a + o.a, s.b + o.b)

    __radd__ = __add__

    def __neg__(s):
        return Q(-s.a, -s.b)

    def __sub__(s, o):
        return s + (-_q(o))

    def __rsub__(s, o):
        return _q(o) + (-s)

    def __mul__(s, o):
        o = _q(o)
        return Q(s.a * o.a + D * s.b * o.b, s.a * o.b + s.b * o.a)

    __rmul__ = __mul__

    def inv(s):
        den = s.a * s.a - D * s.b * s.b
        if den == 0:
            raise ZeroDivisionError("division by zero in Q(sqrt(%d))" % D)
        return Q(s.a / den, -s.b / den)

    def __truediv__(s, o):
        return s * _q(o).inv()

    def __rtruediv__(s, o):
        return _q(o) * s.inv()

    def __eq__(s, o):
        o = _q(o)
        return s.a == o.a and s.b == o.b

    def __ne__(s, o):
        return not s.__eq__(o)

    def __hash__(s):
        return hash((s.a, s.b))

    def is_zero(s):
        return s.a == 0 and s.b == 0

    def sign(s):
        """Exact sign, by comparing a^2 with D*b^2.  No square roots."""
        if s.a == 0 and s.b == 0:
            return 0
        if s.b == 0:
            return 1 if s.a > 0 else -1
        if s.a == 0:
            return 1 if s.b > 0 else -1
        if s.a > 0 and s.b > 0:
            return 1
        if s.a < 0 and s.b < 0:
            return -1
        rational_part_bigger = s.a * s.a > D * s.b * s.b
        if s.a > 0:                                  # a > 0 > b
            return 1 if rational_part_bigger else -1
        return -1 if rational_part_bigger else 1     # a < 0 < b

    def __float__(s):
        return float(s.a) + float(s.b) * (D ** 0.5)

    def __repr__(s):
        if s.b == 0:
            return str(s.a)
        if s.a == 0:
            return "%s*sqrt(%d)" % (s.b, D)
        return "(%s + %s*sqrt(%d))" % (s.a, s.b, D)


def _q(x):
    return x if isinstance(x, Q) else Q(x)


ZERO, ONE = Q(0), Q(1)


# --------------------------------------------------------------------------
# Shared linear algebra.  Matrices are dicts of dicts keyed by vertex label,
# so that a Schur complement can simply forget the eliminated labels.
# --------------------------------------------------------------------------

def as_dict(M):
    n = len(M)
    return dict((i, dict((j, M[i][j]) for j in range(n))) for i in range(n))


def pivot(Mc, surv, p):
    """One elimination step: return (A/A_{S + p}) and the new survivor list."""
    rest = [v for v in surv if v != p]
    d = Mc[p][p]
    out = {}
    for j in rest:
        out[j] = dict((k, Mc[j][k] - Mc[j][p] * Mc[p][k] / d) for k in rest)
    return out, rest


def det(M):
    """Exact determinant by Gaussian elimination over Q(sqrt(D))."""
    M = [row[:] for row in M]
    n = len(M)
    d = ONE
    for c in range(n):
        p = None
        for r in range(c, n):
            if not M[r][c].is_zero():
                p = r
                break
        if p is None:
            return ZERO
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d = d * M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if not f.is_zero():
                for k in range(c, n):
                    M[r][k] = M[r][k] - f * M[c][k]
    return d


def submatrix(M, idx):
    return [[M[i][j] for j in idx] for i in idx]


def cholesky_pivots(M):
    """The pivots D_j of the unpermuted factorization; all > 0 iff SPD."""
    n = len(M)
    Mc, surv, out = as_dict(M), list(range(n)), []
    for _ in range(n):
        out.append(Mc[surv[0]][surv[0]])
        if len(surv) > 1:
            Mc, surv = pivot(Mc, surv, surv[0])
    return out


def char_poly(M):
    """Coefficients of det(xI - M), highest degree first (Faddeev-LeVerrier)."""
    n = len(M)
    coeffs = [ONE]
    Mk = [[ZERO] * n for _ in range(n)]
    for k in range(1, n + 1):
        if k == 1:
            Mk = [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]
        else:
            prod = []
            for i in range(n):
                row = []
                for j in range(n):
                    acc = ZERO
                    for t in range(n):
                        acc = acc + M[i][t] * Mk[t][j]
                    row.append(acc)
                prod.append(row)
            for i in range(n):
                prod[i][i] = prod[i][i] + coeffs[-1]
            Mk = prod
        tr = ZERO
        for i in range(n):
            for t in range(n):
                tr = tr + M[i][t] * Mk[t][i]
        coeffs.append(-tr / k)
    return coeffs


def poly_eval(coeffs, x):
    v = ZERO
    for c in coeffs:
        v = v * x + c
    return v


def zero_pairs(Mc, surv):
    out = []
    for ii, j in enumerate(surv):
        for k in surv[ii + 1:]:
            if Mc[j][k].is_zero():
                out.append((j, k))
    return out


def show(Mc, surv, indent="      "):
    """Print a Schur complement with its surviving labels."""
    cells = {}
    for i in surv:
        for j in surv:
            v = Mc[i][j]
            cells[(i, j)] = str(v.a) if v.b == 0 else "%.6f" % float(v)
    w = max(len(s) for s in cells.values()) if cells else 1
    print(indent + "     " + "  ".join(str(j).rjust(w) for j in surv))
    for i in surv:
        print(indent + str(i).rjust(3) + "  " +
              "  ".join(cells[(i, j)].rjust(w) for j in surv))


def clean(order, M, verbose=False):
    """Is `order` clean for M?

    An ordering is clean iff at every step every off-diagonal entry in the
    pivot's row (among survivors) is nonzero.  Those entries are exactly the
    column of L committed at that step (Definition 'factor entry'), and both
    matrices here have a COMPLETE pattern graph, so every one of them is a
    predicted-nonzero position and no separate fill-graph computation is
    needed.  Returns (is_clean, first_offence or None).
    """
    Mc, surv = as_dict(M), list(range(len(M)))
    for step, p in enumerate(order):
        if verbose:
            z = zero_pairs(Mc, surv)
            print("      stage %d: level {%s}, pivot %d; zeros among survivors: %s"
                  % (step, ", ".join(str(v) for v in order[:step]), p,
                     z if z else "none"))
            if len(M) <= 4:
                show(Mc, surv)
        for k in surv:
            if k != p and Mc[p][k].is_zero():
                if verbose:
                    print("        ^ position (%d,%d) is zero and is committed now"
                          " -> ordering is dirty" % (p, k))
                return False, (step, p, k)
        if len(surv) > 1:
            Mc, surv = pivot(Mc, surv, p)
    return True, None


# --------------------------------------------------------------------------
# Part A: A*, the order-4 counterexample to the First-Schur Conjecture.
# --------------------------------------------------------------------------

ASTAR = [[Q(x) for x in row] for row in
         [[4, -2, -2, -1],
          [-2, 4, 1, 2],
          [-2, 1, 4, 2],
          [-1, 2, 2, 4]]]


def part_a(dump_all=False):
    n = 4
    print("=" * 74)
    print("PART A -- A* (order 4):  Conjecture 2 is false, Conjecture 1 survives")
    print("=" * 74)

    print("\nA1. A* is symmetric positive definite")
    check(all(ASTAR[i][j] == ASTAR[j][i] for i in range(n) for j in range(n)),
          "A* is symmetric")
    minors = [det(submatrix(ASTAR, list(range(m)))) for m in range(1, n + 1)]
    check(all(m.sign() > 0 for m in minors),
          "leading principal minors all > 0: " + ", ".join(str(m) for m in minors))

    print("\nA2. The spectrum is {9,3,3,1}")
    cp = char_poly(ASTAR)
    print("       det(xI - A*) = " +
          " ".join(("+ " if c.sign() >= 0 else "- ") + str(abs(c.a)) + "x^" + str(n - i)
                   for i, c in enumerate(cp)))
    for lam, mult in [(9, 1), (3, 2), (1, 1)]:
        check(poly_eval(cp, Q(lam)).is_zero(),
              "x = %d is a root (claimed multiplicity %d)" % (lam, mult))
    check(cp[1] == Q(-16), "trace = 16 = 9+3+3+1")
    check(det(ASTAR) == Q(81), "det = 81 = 9*3*3*1")

    print("\nA3. The pattern graph is K_4, so every position is predicted nonzero")
    check(all(not ASTAR[i][j].is_zero() for i in range(n) for j in range(n) if i != j),
          "every off-diagonal entry of A* is nonzero")

    print("\nA4. Conjecture 2: every ordering cancels in the FIRST Schur complement")
    print("    The first Schur complement depends only on the first pivot, so the")
    print("    24 orderings give just four distinct matrices A*/A*_{p}:")
    firsts = {}
    for p in range(n):
        S, rest = pivot(as_dict(ASTAR), list(range(n)), p)
        z = zero_pairs(S, rest)
        firsts[p] = z
        print("\n    first pivot p = %d:   A*/A*_{%d}  on survivors %s" % (p, p, rest))
        show(S, rest)
        check(len(z) > 0,
              "has a zero at a predicted-nonzero position: %s" % (z,))
    stage1 = sum(1 for o in permutations(range(n)) if not firsts[o[0]])
    print()
    check(stage1 == 0, "orderings clean at stage 1: %d of 24" % stage1)

    print("\nA5. Conjecture 1: the FACTOR is nevertheless clean for 8 of the 24")
    good = [o for o in permutations(range(n)) if clean(o, ASTAR)[0]]
    print("       clean orderings: " +
          ", ".join("".join(str(v) for v in o) for o in good))
    check(len(good) == 8, "clean factor orderings: %d of 24" % len(good))
    partner = {0: 3, 3: 0, 1: 2, 2: 1}          # the pairing {0,3}, {1,2}
    check(all(o[1] == partner[o[0]] for o in good),
          "every clean ordering pivots the pairing partner second "
          "(pairing {0,3},{1,2}) -- this is the refill mechanism")

    print("\nA6. The refill mechanism, side by side")
    print("\n    (0,3,1,2) is clean.  Pivoting 0 zeroes (1,2), but 3 is pivoted next")
    print("    and refills it before anything commits it:")
    clean((0, 3, 1, 2), ASTAR, verbose=True)
    print("\n    (0,1,2,3) is dirty.  Pivoting 0 zeroes (1,2) and 1 comes next, so")
    print("    (1,2) is committed to L while still zero:")
    clean((0, 1, 2, 3), ASTAR, verbose=True)

    if dump_all:
        print("\nA7. --all: every stage of all 24 orderings")
        for o in permutations(range(n)):
            good_o, bad = clean(o, ASTAR)
            tag = "CLEAN" if good_o else ("dirty, first committed zero %s at stage %d"
                                          % (bad[1:], bad[0]))
            print("\n" + "-" * 66)
            print("    ordering %s: %s" % ("".join(str(v) for v in o), tag))
            print("-" * 66)
            clean(o, ASTAR, verbose=True)


# --------------------------------------------------------------------------
# Part B: M_6, the order-6 counterexample to the Fill-Graph Conjecture.
# --------------------------------------------------------------------------

B_PARAM = Q(F(1, 2))
A_PARAM = Q(F(-3, 8), F(1, 8))          # (-3 + sqrt(73))/8
AB_PARAM = A_PARAM * B_PARAM


def build(m):
    """M_{2m}: vertices 0..2m-1, paired {2k, 2k+1}."""
    n = 2 * m
    M = [[ZERO] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                M[i][j] = ONE
            elif i // 2 == j // 2:
                M[i][j] = AB_PARAM                 # within a pair
            elif i % 2 == j % 2:
                M[i][j] = A_PARAM                  # cross pair, same position
            else:
                M[i][j] = B_PARAM                  # cross pair, opposite
    return M


def part_b(show_stages=False, do_m8=False):
    m, n = 3, 6
    M6 = build(m)
    print("\n" + "=" * 74)
    print("PART B -- M_6 (order 6):  Conjecture 1 is false")
    print("=" * 74)

    print("\nB1. The parameters lie on the forced curve")
    curve = A_PARAM * A_PARAM + (ONE - B_PARAM * B_PARAM) * A_PARAM - ONE
    check(curve.is_zero(), "A^2 + (1-B^2)A - 1 = 0 holds exactly")
    print("       A  = %s ~ %.10f" % (A_PARAM, float(A_PARAM)))
    print("       B  = %s" % B_PARAM)
    print("       AB = %s ~ %.10f" % (AB_PARAM, float(AB_PARAM)))

    print("\nB2. M_6 is symmetric, has pattern K_6, and is positive definite")
    check(all(M6[i][j] == M6[j][i] for i in range(n) for j in range(n)),
          "M_6 is symmetric")
    check(all(not M6[i][j].is_zero() for i in range(n) for j in range(n) if i != j),
          "every off-diagonal entry is nonzero: G = K_6, connected, so M_6 is irreducible")
    piv = cholesky_pivots(M6)
    check(all(p.sign() > 0 for p in piv),
          "all 6 Cholesky pivots are > 0 by exact sign test, so M_6 is SPD")
    print("       pivots ~ " + ", ".join("%.6f" % float(p) for p in piv))
    lams = [(ONE + AB_PARAM + (A_PARAM + B_PARAM) * (m - 1), 1, "1+AB+(A+B)(m-1)"),
            (ONE - AB_PARAM + (A_PARAM - B_PARAM) * (m - 1), 1, "1-AB+(A-B)(m-1)"),
            ((ONE - A_PARAM) * (ONE - B_PARAM), m - 1, "(1-A)(1-B)"),
            ((ONE - A_PARAM) * (ONE + B_PARAM), m - 1, "(1-A)(1+B)")]
    for lam, mult, name in lams:
        shifted = [[M6[i][j] - (lam if i == j else ZERO) for j in range(n)]
                   for i in range(n)]
        check(det(shifted).is_zero() and lam.sign() > 0,
              "lambda = %s ~ %.10f > 0 is an eigenvalue of multiplicity %d"
              % (name, float(lam), mult))
    tr = ZERO
    for i in range(n):
        tr = tr + M6[i][i]
    acc = ZERO
    for lam, mult, _ in lams:
        acc = acc + lam * mult
    check(acc == tr, "the eigenvalues sum to the trace (= 6)")
    prod = ONE
    for lam, mult, _ in lams:
        for _ in range(mult):
            prod = prod * lam
    check(prod == det(M6), "the eigenvalues multiply to det M_6")

    print("\nB3. Proof step 1: after any first pivot the zeros are exactly a perfect")
    print("    matching on the other pairs -- and proof step 2: the partner avoids them")
    for p0 in range(n):
        S, rest = pivot(as_dict(M6), list(range(n)), p0)
        z = zero_pairs(S, rest)
        expect = sorted((2 * k, 2 * k + 1) for k in range(m) if k != p0 // 2)
        q0 = p0 ^ 1
        check(sorted(z) == expect,
              "p0 = %d: zero set %s is the matching on the other pairs" % (p0, z))
        check(all(q0 not in pair for pair in z),
              "p0 = %d: partner q0 = %d meets no zero, so the second pivot is forced"
              % (p0, q0))

    print("\nB4. Proof step 5: after the forced pivot, the zeros cover every survivor")
    for p0 in range(n):
        q0 = p0 ^ 1
        S, rest = pivot(as_dict(M6), list(range(n)), p0)
        S2, rest2 = pivot(S, rest, q0)
        z = zero_pairs(S2, rest2)
        covered = set()
        for pair in z:
            covered.update(pair)
        check(covered == set(rest2),
              "p0 = %d, q0 = %d: zeros %s cover survivors %s, so the third pivot "
              "reads a zero" % (p0, q0, z, rest2))

    print("\nB5. The conclusion: no ordering of M_6 is clean")
    good = [o for o in permutations(range(n)) if clean(o, M6)[0]]
    check(len(good) == 0, "clean orderings: %d of 720" % len(good))
    hist = {}
    for o in permutations(range(n)):
        _, bad = clean(o, M6)
        hist[bad[0]] = hist.get(bad[0], 0) + 1
    print("       stage at which the first committed zero appears:")
    for st in sorted(hist):
        print("         stage %d: %d orderings" % (st, hist[st]))
    check(hist.get(2, 0) == n * 24,
          "exactly %d = 6 * 4! orderings reach stage 2 -- precisely those that take "
          "the forced partner second" % (n * 24,))

    if show_stages:
        print("\nB6. The forced opening, stage by stage (first pivot 0, so q0 = 1)")
        clean((0, 1, 2, 3, 4, 5), M6, verbose=True)
        print("\n    and if the forced second pivot is NOT taken (0 then 2):")
        clean((0, 2, 1, 3, 4, 5), M6, verbose=True)

    if do_m8:
        print("\nB7. --m8: the same at order 8 (40320 orderings; this takes a while)")
        M8 = build(4)
        p8 = cholesky_pivots(M8)
        check(all(p.sign() > 0 for p in p8), "M_8 is SPD (8 pivots > 0, exact)")
        g8 = 0
        for o in permutations(range(8)):
            if clean(o, M8)[0]:
                g8 += 1
        check(g8 == 0, "clean orderings of M_8: %d of 40320" % g8)


# --------------------------------------------------------------------------

def main():
    only = None
    if "--only" in sys.argv:
        i = sys.argv.index("--only")
        if i + 1 < len(sys.argv):
            only = sys.argv[i + 1].lower()
    print(__doc__.split("DEPENDENCIES")[0].strip())
    print()
    if only in (None, "astar", "a"):
        part_a(dump_all="--all" in sys.argv)
    if only in (None, "m6", "b", "m8"):
        part_b(show_stages="--show-stages" in sys.argv, do_m8="--m8" in sys.argv)

    print("\n" + "=" * 74)
    print("SUMMARY (%d checks)" % _count[0])
    print("=" * 74)
    if only in (None, "astar", "a"):
        print("  Conjecture 2 (First-Schur): FALSE at order 4.  Witness A*, 0 of 24")
        print("      orderings cancellation-free at stage 1.")
        print("  A* is NOT a counterexample to Conjecture 1: 8 of its 24 orderings")
        print("      give a clean factor, by refill.")
    if only in (None, "m6", "b", "m8"):
        print("  Conjecture 1 (Fill-Graph):   FALSE at order 6.  Witness M_6, 0 of 720")
        print("      orderings clean; the second pivot is forced and the third fails.")
    print()
    print("ALL CHECKS PASSED" if _ok[0] else "SOME CHECKS FAILED")
    return 0 if _ok[0] else 1


if __name__ == "__main__":
    sys.exit(main())
