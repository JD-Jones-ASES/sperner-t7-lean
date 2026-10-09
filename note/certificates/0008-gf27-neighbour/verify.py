#!/usr/bin/env python3
"""Certificate 0008: the Paley tournament on GF(27) has t = 5, and its anti-diagonal is a symmetric
clique of 27 points of its second Sperner power (26 points without 0), so C > t on 27 and on 26
vertices.

GF(27) = F_3[x]/(x^3 - x - 1). The Paley tournament: a -> b iff b - a is a nonzero square (-1 is a
non-square because 27 = 3 mod 4, so this is a tournament). The anti-diagonal is {(a, -a)}. Two of
its points (a, -a) and (b, -b) with a != b carry arcs both ways in the OR-square: b - a and
(-a) - (-b) = -(b - a) are nonzero, and exactly one of them is a square. So the anti-diagonal is a
symmetric clique of the second Sperner power (Alon 1998, Section 4, uses this construction), and
w(Q27^2) >= 27 > 25 = t^2, so C(Q27) >= sqrt(27) > 5 = t(Q27). Removing the point (0, 0) leaves 26
points in the second power of the subtournament on the 26 nonzero elements, whose transitive
number is again 5, so C >= sqrt(26) > 5 there too. That t(Q27) = 5 is in print (Sanchez-Flores
1998); it is recomputed here.

Standard library only; exact integers; no assert statements. Pinned here: the modulus
x^3 - x - 1 over F_3, t = 5 for both tournaments, and the sizes 27 and 26. Checks:

  1. The field: x^3 - x - 1 has no root in F_3 (so the cubic is irreducible); the implemented
     product is commutative, associative and distributive over the addition on all of GF(27)^3;
     every nonzero element is invertible.
  2. 13 nonzero squares; -1 is a non-square; the Paley relation is a tournament.
  3. t = 5 for Q27 by two routes (source peeling on bitmasks; the no-3-cycle test on every 5- and
     6-subset: some transitive 5-set, no transitive 6-set), and t = 5 for the 26-vertex
     subtournament by source peeling.
  4. Each anti-diagonal: distinct points; no arc of the strong square between any two of them;
     every ordered pair of distinct points has a forward coordinate; 27 > 25 and 26 > 25.

Forged controls run automatically (each must FAIL): the reducible modulus x^3 - x; t claimed to be
4; the diagonal {(a, a)} in place of the anti-diagonal; one anti-diagonal point (1, -1) moved to
(1, 0). The last line is VERDICT: PASS or VERDICT: FAIL; the exit status is 0 only on PASS.

Usage: python -O verify.py
"""
import itertools
import sys

MODULUS_PINNED = (1, 1)   # x^3 = c0 + c1 x, i.e. x^3 - x - 1
T_PINNED = 5
SIZES_PINNED = (27, 26)


class Fail(Exception):
    pass


def check(modulus, t_claim, build, say):
    c0, c1 = modulus
    E = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]   # a + b x + c x^2
    ZERO = (0, 0, 0)
    ONE = (1, 0, 0)

    def add(u, v):
        return tuple((p + q) % 3 for p, q in zip(u, v))

    def neg(u):
        return tuple((-p) % 3 for p in u)

    def sub(u, v):
        return add(u, neg(v))

    def mul(u, v):
        r = [0] * 5
        for i in range(3):
            for j in range(3):
                r[i + j] += u[i] * v[j]
        # x^4 = x * x^3 = c0 x + c1 x^2, then x^3 = c0 + c1 x
        r[1] += c0 * r[4]
        r[2] += c1 * r[4]
        r[0] += c0 * r[3]
        r[1] += c1 * r[3]
        return (r[0] % 3, r[1] % 3, r[2] % 3)

    # 1. the field
    if any((s ** 3 - c1 * s - c0) % 3 == 0 for s in range(3)):
        raise Fail("the modulus x^3 - (%d + %d x) has a root in F_3, so it is reducible" % (c0, c1))
    for u in E:
        for v in E:
            uv = mul(u, v)
            if uv != mul(v, u):
                raise Fail("the product is not commutative")
            for w in E:
                if mul(uv, w) != mul(u, mul(v, w)):
                    raise Fail("the product is not associative")
                if mul(u, add(v, w)) != add(uv, mul(u, w)):
                    raise Fail("the product does not distribute")
    if not all(any(mul(u, v) == ONE for v in E) for u in E if u != ZERO):
        raise Fail("a nonzero element has no inverse")
    say("1. GF(27) = F_3[x]/(x^3 - x - 1): the cubic has no root in F_3; the product is commutative, "
        "associative and distributive on all 27^3 triples; every nonzero element is invertible")
    # 2. squares and the tournament
    SQ = {mul(u, u) for u in E if u != ZERO}
    if len(SQ) != 13 or neg(ONE) in SQ:
        raise Fail("%d nonzero squares; -1 a square: %s" % (len(SQ), neg(ONE) in SQ))

    def arc(a, b):
        return a != b and sub(b, a) in SQ

    if any(arc(a, b) == arc(b, a) for a, b in itertools.combinations(E, 2)) or any(arc(a, a) for a in E):
        raise Fail("the Paley relation is not a tournament")
    say("2. 13 nonzero squares; -1 is a non-square; the Paley relation on GF(27) is a tournament")
    # 3. t by two routes
    idx = {e: i for i, e in enumerate(E)}
    out = [0] * 27
    for a in E:
        for b in E:
            if arc(a, b):
                out[idx[a]] |= 1 << idx[b]
    memo = {}

    def tt(mask):
        if mask == 0:
            return 0
        if mask in memo:
            return memo[mask]
        best = 0
        m = mask
        while m:
            v = (m & -m).bit_length() - 1
            m &= m - 1
            r = 1 + tt(mask & out[v])
            if r > best:
                best = r
        memo[mask] = best
        return best

    t27 = tt((1 << 27) - 1)
    t26 = tt(((1 << 27) - 1) & ~(1 << idx[ZERO]))
    if t27 != t_claim or t26 != t_claim:
        raise Fail("source peeling gives t = %d (27 vertices) and %d (26 vertices); claimed %d" % (t27, t26, t_claim))

    def trans(S):
        for a, b, c in itertools.combinations(S, 3):
            if (arc(a, b) and arc(b, c) and arc(c, a)) or (arc(b, a) and arc(c, b) and arc(a, c)):
                return False
        return True

    has = any(trans(S) for S in itertools.combinations(E, t_claim))
    count_next = sum(1 for S in itertools.combinations(E, t_claim + 1) if trans(S))
    if not has or count_next != 0:
        raise Fail("no-3-cycle test: a transitive %d-set %s; transitive %d-sets %d"
                   % (t_claim, has, t_claim + 1, count_next))
    say("3. t = %d by source peeling (27 vertices; also the 26 nonzero elements) and by the no-3-cycle test "
        "(a transitive %d-set exists; none of the %d-subsets is transitive)"
        % (t_claim, t_claim, t_claim + 1))
    # 4. the anti-diagonals
    def strong(u, v):
        return u != v and all(p == q or arc(p, q) for p, q in zip(u, v))

    def ordom(u, v):
        return any(arc(p, q) for p, q in zip(u, v))

    for size, base in zip(SIZES_PINNED, (E, [e for e in E if e != ZERO])):
        S = build(base, neg)
        if len(S) != size or len(set(S)) != size:
            raise Fail("the set has %d distinct points, %d expected" % (len(set(S)), size))
        if any(p not in idx for q in S for p in q):
            raise Fail("a point lies outside GF(27)^2")
        if size == 26 and any(p == ZERO for q in S for p in q):
            raise Fail("the 26-point set uses the element 0")
        if any(strong(u, v) for u in S for v in S):
            raise Fail("the %d-point set carries an arc of the strong square" % size)
        if not all(ordom(u, v) for u in S for v in S if u != v):
            raise Fail("the %d-point set is not a symmetric clique of the OR-square" % size)
        if not size > t_claim ** 2:
            raise Fail("%d does not exceed %d" % (size, t_claim ** 2))
        say("4. the %d-point anti-diagonal: no strong-square arc; every ordered pair has a forward coordinate; "
            "%d > %d" % (size, size, t_claim ** 2))
    if (c0, c1) != MODULUS_PINNED or t_claim != T_PINNED:
        raise Fail("the constants are not the statement's")
    return "w(Q27^2) >= 27 > 25 = t(Q27)^2, so C(Q27) >= sqrt(27) > 5; on 26 vertices C >= sqrt(26) > 5 = t"


def anti(base, neg):
    return [(a, neg(a)) for a in base]


def run(modulus, t_claim, build, say):
    try:
        return True, check(modulus, t_claim, build, say)
    except Fail as e:
        return False, str(e)


def main():
    ok, msg = run(MODULUS_PINNED, T_PINNED, anti, print)
    print(("PASS: " if ok else "FAIL: ") + msg)
    verdict = ok

    def diagonal(base, neg):
        return [(a, a) for a in base]

    def moved(base, neg):
        S = [(a, neg(a)) for a in base]
        return [((1, 0, 0), (0, 0, 0)) if q == ((1, 0, 0), (2, 0, 0)) else q for q in S]

    controls = [("the reducible modulus x^3 - x", (0, 1), T_PINNED, anti),
                ("t claimed to be 4", MODULUS_PINNED, 4, anti),
                ("the diagonal in place of the anti-diagonal", MODULUS_PINNED, T_PINNED, diagonal),
                ("the point (1, -1) moved to (1, 0)", MODULUS_PINNED, T_PINNED, moved)]
    for name, mod, tc, build in controls:
        fok, fmsg = run(mod, tc, build, lambda s: None)
        print("control (%s): %s -- %s" % (name, "FAIL as expected" if not fok else "PASSED, which is wrong", fmsg))
        if fok:
            verdict = False
    print("VERDICT: PASS" if verdict else "VERDICT: FAIL")
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
