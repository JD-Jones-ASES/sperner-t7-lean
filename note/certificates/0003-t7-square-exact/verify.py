#!/usr/bin/env python3
"""Certificate 0003: the largest transitive clique of the second Sperner power of T7 has exactly
18 points.

T7 = Q23[W], W = {0, 1, 2, 3, 9, 14, 18}, x -> y iff y - x is a nonzero square mod 23. A transitive
clique of the second Sperner (OR) power is a list of points of W x W in which every earlier point
sends an arc to every later one in some coordinate. Because T7 is a tournament, these are exactly
the acyclic sets of the directed strong square T7 [x] T7 (u -> v there iff u != v and each
coordinate is equal or an arc), taken in a topological order. Claim: tr(T7^2) = 18.

Standard library only; exact integers; no assert statements (python -O changes nothing). Reads
witness.json next to this file (or the file named on the command line):

    {"p": 23, "W": [seven residues], "t": 4, "value": 18, "order": [[a, b], ...]}

The statement constants are pinned in this file (P, W, t and the value 18); a file with other
constants fails. Checks:

  1. T7 is a tournament; t(T7) = 4 by two routes: the score-sequence test on all 128 subsets, and
     an exhaustive search over transitive chains.
  2. LOWER BOUND: "order" lists 18 distinct points of W x W, every earlier point OR-dominates every
     later one; independently, Kahn's algorithm on the strong-square arcs (rebuilt from the
     definition) empties the set, so it is acyclic.
  3. UPPER BOUND, by an exhaustive search of its own: a Russian-doll search over the 49 vertices
     of the strong square computes g[k], the largest acyclic set inside {v_k, ..., v_48}, for
     k = 48 down to 0. Bounds used inside the search, all valid: heredity (an acyclic set inside
     {v_j, ...} has at most g[j] points) and the row and column cap (an acyclic set meets each row
     {a} x W and each column W x {b} in a transitive subtournament of T7, so in at most t points).
     The search stops with FAIL as soon as some g[k] exceeds the claimed value, and the claimed
     value must equal g[0].
  4. The lift: 18 > 16 = t^2; the least m with 18^m > (17 m + 1) 16^m is 59 (a symmetric clique
     of more than 4^118 words in T7^118), and the least m for which the largest coefficient of
     (1 + x + ... + x^17)^m exceeds 16^m is 38 (more than 4^76 words in T7^76).

Usage:
    python -O verify.py                          full check, about 10 minutes; VERDICT: PASS
    python -O verify.py --lower                  steps 1, 2 and 4 only; it says the upper bound
                                                 was not checked (proves tr(T7^2) >= 18 only)
    python -O verify.py witness_FORGED_17max.json   must end VERDICT: FAIL (about 4 minutes)

Forged controls run automatically after the main check (each must FAIL, and each fails before the
search): two points swapped; t claimed to be 3; a vertex of W replaced; the value claimed to be 19.
If the environment variable VERIFY_STOP_FILE names an existing file, the search stops with no
verdict (VERDICT: FAIL). The last line is VERDICT: PASS or VERDICT: FAIL; the exit status is 0
only on PASS.
"""
import json
import os
import sys

P = 23
W_PINNED = [0, 1, 2, 3, 9, 14, 18]
T_PINNED = 4
VALUE_PINNED = 18
LIFT_PINNED = (59, 38)


class Fail(Exception):
    pass


def stop_requested():
    path = os.environ.get("VERIFY_STOP_FILE")
    return bool(path) and os.path.exists(path)


def check(cert, lower_only, say):
    """Raise Fail on any error; return a one-line summary on success."""
    p = int(cert["p"])
    W = [int(x) for x in cert["W"]]
    t = int(cert["t"])
    value = int(cert["value"])
    order = [tuple(int(c) for c in q) for q in cert["order"]]
    if p != P or W != W_PINNED:
        raise Fail("the file's constants (p, W) = (%d, %s) are not the statement's (23, %s)" % (p, W, W_PINNED))
    n7 = len(W)
    squares = {x * x % P for x in range(1, P)}

    def arc(x, y):
        return x != y and ((y - x) % P) in squares

    # 1. a tournament, and t by two routes
    for x in W:
        if arc(x, x):
            raise Fail("loop at %d" % x)
        for y in W:
            if x != y and arc(x, y) == arc(y, x):
                raise Fail("not a tournament at (%d, %d)" % (x, y))
    best_t = 0
    for mask in range(1 << n7):
        sub = [W[i] for i in range(n7) if mask >> i & 1]
        sc = sorted(sum(1 for y in sub if arc(x, y)) for x in sub)
        if sc == list(range(len(sub))) and len(sub) > best_t:
            best_t = len(sub)

    def longest_chain(cands, depth):
        best = depth
        for v in cands:
            best = max(best, longest_chain([u for u in cands if arc(v, u)], depth + 1))
        return best

    chain_t = longest_chain(list(W), 0)
    if best_t != t or chain_t != t:
        raise Fail("t(T7) is %d (score test) and %d (chain search); the file says %d" % (best_t, chain_t, t))
    if t != T_PINNED:
        raise Fail("the file's t = %d is not the statement's 4" % t)
    say("1. T7 = Q23[%s] is a tournament; t(T7) = %d (score test on all %d subsets; chain search)"
        % (W, t, 1 << n7))

    # 2. the lower bound
    if len(order) != value:
        raise Fail("the witness has %d points, the claimed value is %d" % (len(order), value))
    if len(set(order)) != len(order):
        raise Fail("a point is repeated in the witness")
    for q in order:
        if q[0] not in W or q[1] not in W:
            raise Fail("point %s lies outside W x W" % (q,))
    for i in range(len(order)):
        for j in range(i + 1, len(order)):
            u, v = order[i], order[j]
            if not (arc(u[0], v[0]) or arc(u[1], v[1])):
                raise Fail("no OR-arc from %s to %s (positions %d < %d)" % (u, v, i, j))

    def strong(u, v):
        return u != v and (u[0] == v[0] or arc(u[0], v[0])) and (u[1] == v[1] or arc(u[1], v[1]))

    indeg = {u: sum(1 for v in order if strong(v, u)) for u in order}
    queue = [u for u in order if indeg[u] == 0]
    done = 0
    while queue:
        u = queue.pop()
        done += 1
        for v in order:
            if strong(u, v):
                indeg[v] -= 1
                if indeg[v] == 0:
                    queue.append(v)
    if done != len(order):
        raise Fail("Kahn's algorithm: the witness is not acyclic in the strong square")
    say("2. LOWER BOUND: %d distinct points; every earlier point OR-dominates every later one; "
        "acyclic in the strong square (Kahn)" % value)

    # 4 (cheap, before the long search). the lift
    tt = t * t
    if not value > tt:
        raise Fail("the value %d does not exceed t^2 = %d" % (value, tt))
    m1 = 1
    while not value ** m1 > ((value - 1) * m1 + 1) * tt ** m1:
        m1 += 1
        if m1 > 10000:
            raise Fail("no pigeonhole exponent below 10000")
    coef = [1]
    m2 = 0
    while True:
        m2 += 1
        new = [0] * (len(coef) + value - 1)
        for i, c in enumerate(coef):
            for k in range(value):
                new[i + k] += c
        coef = new
        if max(coef) > tt ** m2:
            break
        if m2 > 10000:
            raise Fail("no largest-class exponent below 10000")
    say("4. LIFT: %d > %d; pigeonhole at m = %d (a symmetric clique of more than 4^%d words in T7^%d); "
        "largest index-sum class at m = %d (more than 4^%d words in T7^%d)"
        % (value, tt, m1, 2 * m1, 2 * m1, m2, 2 * m2, 2 * m2))

    if lower_only:
        if value != VALUE_PINNED or (m1, m2) != LIFT_PINNED:
            raise Fail("the value %d or the lift exponents %s are not the statement's (18, %s)"
                       % (value, (m1, m2), LIFT_PINNED))
        say("UPPER BOUND NOT CHECKED (--lower): this run proves tr(T7^2) >= %d only" % value)
        return "tr(T7^2) >= %d (lower bound and lift only; the upper bound was not checked)" % value

    # 3. the upper bound: a Russian-doll search
    verts = [(a, b) for a in W for b in W]
    n = len(verts)
    out = [0] * n
    inn = [0] * n
    for s in range(n):
        for r in range(n):
            if strong(verts[s], verts[r]):
                out[s] |= 1 << r
                inn[r] |= 1 << s
    rowm = [0] * n7
    colm = [0] * n7
    for s, (a, b) in enumerate(verts):
        rowm[W.index(a)] |= 1 << s
        colm[W.index(b)] |= 1 << s
    g = [0] * (n + 1)
    nodes = [0]

    def popc(x):
        return bin(x).count("1")

    def reach_of(S, reach, w):
        R = 0
        m = out[w] & S
        while m:
            lb = m & -m
            R |= lb | reach[lb.bit_length() - 1]
            m ^= lb
        return R

    def bound(S, cand):
        if cand == 0:
            return 0
        b = min(g[(cand & -cand).bit_length() - 1], popc(cand))
        b2 = 0
        for L in rowm:
            b2 += max(0, min(t - popc(S & L), popc(cand & L)))
        b3 = 0
        for L in colm:
            b3 += max(0, min(t - popc(S & L), popc(cand & L)))
        return min(b, b2, b3)

    def dfs(S, reach, size, cand, target):
        nodes[0] += 1
        if nodes[0] & 4095 == 0 and stop_requested():
            raise Fail("stop file present; search abandoned (no verdict)")
        if size >= target:
            return True
        keep = 0
        m = cand
        while m:
            lb = m & -m
            w = lb.bit_length() - 1
            if reach_of(S, reach, w) & inn[w] == 0:
                keep |= lb
            m ^= lb
        cand = keep
        while cand:
            if size + bound(S, cand) < target:
                return False
            lb = cand & -cand
            w = lb.bit_length() - 1
            cand ^= lb
            Rw = reach_of(S, reach, w)
            if Rw & inn[w]:
                continue
            nr = dict(reach)
            nr[w] = Rw
            into = inn[w] & S
            m = S
            while m:
                lb2 = m & -m
                u = lb2.bit_length() - 1
                if (lb2 & into) or (reach[u] & into):
                    nr[u] = reach[u] | lb | Rw
                m ^= lb2
            if dfs(S | lb, nr, size + 1, cand, target):
                return True
        return False

    full = (1 << n) - 1
    for k in range(n - 1, -1, -1):
        later = full ^ ((1 << (k + 1)) - 1)
        if dfs(1 << k, {k: 0}, 1, later, g[k + 1] + 1):
            g[k] = g[k + 1] + 1
        else:
            g[k] = g[k + 1]
        if g[k] > value:
            raise Fail("an acyclic set of size %d exists inside vertices %d..48: the claimed maximum %d is wrong"
                       % (g[k], k, value))
    if g[0] != value:
        raise Fail("the exhaustive search gives %d, the file claims %d" % (g[0], value))
    say("3. UPPER BOUND: Russian doll over %d vertices, %d nodes; g = %s; no acyclic set of size %d"
        % (n, nodes[0], g[:n], value + 1))
    if value != VALUE_PINNED or (m1, m2) != LIFT_PINNED:
        raise Fail("the value %d or the lift exponents %s are not the statement's (18, %s)"
                   % (value, (m1, m2), LIFT_PINNED))
    return "tr(T7^2) = a(T7 [x] T7) = %d exactly; sqrt(%d) <= C(T7)" % (value, value)


def run(cert, lower_only, say):
    try:
        return True, check(cert, lower_only, say)
    except Fail as e:
        return False, str(e)
    except (KeyError, ValueError, TypeError) as e:
        return False, "malformed certificate: %r" % (e,)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    lower_only = "--lower" in sys.argv[1:]
    here = os.path.dirname(os.path.abspath(__file__))
    path = args[0] if args else os.path.join(here, "witness.json")
    with open(path) as fh:
        cert = json.load(fh)
    ok, msg = run(cert, lower_only, print)
    print(("PASS: " if ok else "FAIL: ") + msg)
    verdict = ok

    def forged(edit):
        f = json.loads(json.dumps(cert))
        edit(f)
        return f

    def swap(f):
        f["order"][0], f["order"][1] = f["order"][1], f["order"][0]

    def t3(f):
        f["t"] = 3

    def w19(f):
        f["W"] = f["W"][:-1] + [19]

    def v19(f):
        f["value"] = 19

    for name, edit in (("two points swapped", swap), ("t claimed to be 3", t3),
                       ("vertex 18 replaced by 19", w19), ("value claimed to be 19", v19)):
        fok, fmsg = run(forged(edit), True, lambda s: None)
        print("control (%s): %s -- %s" % (name, "FAIL as expected" if not fok else "PASSED, which is wrong", fmsg))
        if fok:
            verdict = False
    print("VERDICT: PASS" if verdict else "VERDICT: FAIL")
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
