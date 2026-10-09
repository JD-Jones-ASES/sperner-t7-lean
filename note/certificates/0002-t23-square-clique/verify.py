#!/usr/bin/env python3
"""Certificate 0002: a transitive clique of the second Sperner power of the Paley tournament on 23
vertices, larger than the square of its transitive number, with the lift.

Standard library only; exact integers; no assert statements (python -O changes nothing). Reads
witness.json next to this file:

    {"p": 23, "W": [all 23 residues], "t": 5, "order": [[a, b], ...], "m_pigeonhole": 49, "m_middle": 33}

and checks, for T = Q_p[W] (x -> y iff y - x is a nonzero square mod p):

  1. T is a tournament on W (irreflexive, exactly one direction between distinct vertices).
  2. t(T) = t by two routes: an exhaustive search over transitive chains (a chain grows only by
     common out-neighbours of its members, so every transitive subtournament is reached in its
     own order; no symmetry is used) finds the longest chain to have t vertices; and the
     score-sequence test on every (t+1)-subset of W finds none transitive (a transitive set of
     any larger size would contain one). Some t-subset passes both tests.
  3. "order" lists |order| distinct points of W x W, and for i < j some coordinate carries an arc
     from order[i] to order[j] (a transitive clique of the OR-square); independently, every arc of
     the directed strong product T [x] T between points of the set runs forward in the order.
  4. The lift: N = |order| > t^2; with m = m_pigeonhole, N^m > ((N-1) m + 1) (t^2)^m exactly, so some
     equal-index-sum class of the N^m words of length m has more than (t^2)^m words, and two
     distinct equal-sum words carry OR-arcs in both directions in T^(2m): w(T^(2m)) > t^(2m); and the
     middle coefficient of (1 + x + ... + x^(N-1))^m_middle exceeds (t^2)^m_middle, the same
     conclusion at n = 2 m_middle.

Forged controls (run automatically; each must FAIL): the order reversed; t claimed one smaller;
the last point dropped; a point duplicated. The last line is VERDICT: PASS or VERDICT: FAIL; the
exit status is 0 only on PASS.
"""
import itertools
import json
import os
import sys


def check(cert):
    """Return (ok, message) for one certificate dictionary."""
    p = int(cert["p"])
    W = list(cert["W"])
    t = int(cert["t"])
    order = [tuple(q) for q in cert["order"]]
    m1 = int(cert["m_pigeonhole"])
    m2 = int(cert["m_middle"])
    if p < 3 or any(p % d == 0 for d in range(2, int(p ** 0.5) + 1)) or p % 4 != 3:
        return False, "p must be a prime congruent to 3 mod 4"
    squares = {(x * x) % p for x in range(1, p)}

    def arc(a, b):
        return a != b and ((b - a) % p) in squares

    # 1. a tournament on W
    if len(set(W)) != len(W) or any(not (0 <= w < p) for w in W):
        return False, "W is not a set of residues mod p"
    for a in W:
        if arc(a, a):
            return False, "loop at %d" % a
        for b in W:
            if a != b and arc(a, b) == arc(b, a):
                return False, "not a tournament at (%d, %d)" % (a, b)

    # 2. t(T) = t, two routes
    out = {a: [b for b in W if arc(a, b)] for a in W}

    def longest_chain(candidates, depth):
        best = depth
        for v in candidates:
            nxt = [u for u in candidates if arc(v, u)]
            L = longest_chain(nxt, depth + 1)
            if L > best:
                best = L
        return best

    tt = longest_chain(list(W), 0)
    if tt != t:
        return False, "the longest transitive chain has %d vertices, not %d" % (tt, t)

    def transitive_by_scores(sub):
        return sorted(sum(1 for b in sub if arc(a, b)) for a in sub) == list(range(len(sub)))

    for sub in itertools.combinations(W, t + 1):
        if transitive_by_scores(sub):
            return False, "transitive %d-set %s (score test)" % (t + 1, sub)
    if not any(transitive_by_scores(sub) for sub in itertools.combinations(W, t)):
        return False, "no transitive %d-set (score test)" % t

    # 3. the clique and its order
    N = len(order)
    if len(set(order)) != N:
        return False, "repeated point in the order"
    if any(q[0] not in W or q[1] not in W for q in order):
        return False, "a point lies outside W x W"

    def or_arc(u, v):
        return arc(u[0], v[0]) or arc(u[1], v[1])

    for i in range(N):
        for j in range(i + 1, N):
            if not or_arc(order[i], order[j]):
                return False, "no OR-arc from %s to %s" % (order[i], order[j])

    def strong_arc(u, v):
        if u == v:
            return False
        return (arc(u[0], v[0]) or u[0] == v[0]) and (arc(u[1], v[1]) or u[1] == v[1])

    pos = {q: i for i, q in enumerate(order)}
    for u in order:
        for v in order:
            if strong_arc(u, v) and pos[u] > pos[v]:
                return False, "strong-product arc %s -> %s runs backward" % (u, v)

    # 4. the lift
    t2 = t * t
    if not N > t2:
        return False, "N = %d does not exceed t^2 = %d" % (N, t2)
    if not N ** m1 > ((N - 1) * m1 + 1) * t2 ** m1:
        return False, "pigeonhole inequality fails at m = %d" % m1
    coef = [1]
    for _ in range(m2):
        new = [0] * (len(coef) + N - 1)
        for i, c in enumerate(coef):
            for k in range(N):
                new[i + k] += c
        coef = new
    if not max(coef) > t2 ** m2:
        return False, "middle-coefficient inequality fails at m = %d" % m2
    return True, ("Q_%d[%s] is a tournament with t = %d (chain search and score test); %d distinct points "
                  "form a transitive clique of the OR-square (acyclic in the strong square); %d > %d; the "
                  "pigeonhole lift holds at m = %d (n = %d) and the middle coefficient at m = %d (n = %d)."
                  % (p, W, t, N, N, t2, m1, 2 * m1, m2, 2 * m2))


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "witness.json")) as fh:
        cert = json.load(fh)
    ok, msg = check(cert)
    print(("PASS: " if ok else "FAIL: ") + msg)
    verdict = ok
    controls = []
    forged = json.loads(json.dumps(cert))
    forged["order"] = list(reversed(forged["order"]))
    controls.append(("order reversed", forged))
    forged = json.loads(json.dumps(cert))
    forged["t"] = int(forged["t"]) - 1
    controls.append(("t claimed one smaller", forged))
    forged = json.loads(json.dumps(cert))
    forged["order"] = forged["order"][:-1]
    controls.append(("last point dropped", forged))
    forged = json.loads(json.dumps(cert))
    forged["order"][1] = forged["order"][0]
    controls.append(("a point duplicated", forged))
    for name, f in controls:
        fok, fmsg = check(f)
        print("control (%s): %s -- %s" % (name, "FAIL as expected" if not fok else "PASSED, which is wrong", fmsg))
        if fok:
            verdict = False
    print("VERDICT: PASS" if verdict else "VERDICT: FAIL")
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
