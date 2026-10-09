#!/usr/bin/env python3
"""Certificate 0007: witnesses for the small powers of T7: tr(T7^2) >= 18, tr(T7^3) >= 75,
w(T7^3) >= 16, and w(T7^2) = 7.

T7 = Q23[W], W = {0, 1, 2, 3, 9, 14, 18}, x -> y iff y - x is a nonzero square mod 23. For words of
length n over W:
  * a transitive clique of the n-th Sperner (OR) power is a list in which every earlier word has
    a coordinate carrying an arc to every later word; tr(T7^n) is the largest size. Because T7 is
    a tournament these are the acyclic sets of the strong power (u -> v iff u != v and each
    coordinate is equal or an arc), in a topological order.
  * a symmetric clique is a set in which every ordered pair of distinct words has such a
    coordinate; w(T7^n) is the largest size (Alon 1998), and C(T7) = sup_n w(T7^n)^(1/n).

Standard library only; exact integers; no assert statements. Reads witnesses.json next to this
file. Pinned here: p = 23, W, t = 4, and the sizes 18 and 75 (transitive cliques of the square
and the cube) and 7 and 16 (symmetric cliques of the square and the cube). Checks:

  1. T7 is a tournament; t(T7) = 4 (an ordering search on every 5-subset and 4-subset).
  2. Each transitive clique, two routes: forward OR-domination in the listed order; no strong-power
     arc runs backward, and Kahn's algorithm on the strong-power arcs (rebuilt from the
     definition) empties the set.
  3. Each symmetric clique: every ordered pair of distinct words has a forward coordinate.
  4. w(T7^2) <= 7 (so = 7), by checking the finite fact behind the injection argument: two
     distinct points of W x W that share a coordinate never carry OR-arcs in both directions, so a
     symmetric clique of the square has distinct first coordinates. Also: among the 5040
     bijections s of W, exactly one makes {(x, s(x))} a symmetric clique, and it is the listed
     7-set (the graph of the anti-automorphism 0 <-> 3, 1 <-> 18, 9 <-> 14, 2 fixed).
  5. The comparisons, in exact integers: 18^1 > 4^2 (the square exceeds t^2); 75^2 < 18^3 (the
     cube does not improve sqrt(18)); 16 < 4^3 and 7 < 4^2 (no symmetric clique exceeds 4^n at
     n = 2, 3); and the least m for which the largest coefficient of (1 + ... + x^17)^m exceeds
     16^m is 38 (a symmetric clique of more than 4^76 words in T7^76).

Forged controls run automatically (each must FAIL): the first two words of the square clique
swapped; the word (0, 0, 0) added to the cube's symmetric clique; the square clique cut to 16
words; a vertex of W replaced. The last line is VERDICT: PASS or VERDICT: FAIL; the exit status is
0 only on PASS.

Usage: python -O verify.py
"""
import itertools
import json
import os
import sys

P = 23
W_PINNED = [0, 1, 2, 3, 9, 14, 18]
T_PINNED = 4
TR_PINNED = {2: 18, 3: 75}
SYM_PINNED = {2: 7, 3: 16}
LIFT_PINNED = 38
SQ = {(x * x) % P for x in range(1, P)}


def arc(a, b):
    return a != b and ((b - a) % P) in SQ


def ordom(u, v):
    return any(arc(a, b) for a, b in zip(u, v))


def sarc(u, v):
    return u != v and all(a == b or arc(a, b) for a, b in zip(u, v))


def kahn_acyclic(S):
    k = len(S)
    indeg = [0] * k
    out = [[] for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if sarc(S[i], S[j]):
                out[i].append(j)
                indeg[j] += 1
    stack = [i for i in range(k) if indeg[i] == 0]
    seen = 0
    while stack:
        i = stack.pop()
        seen += 1
        for j in out[i]:
            indeg[j] -= 1
            if indeg[j] == 0:
                stack.append(j)
    return seen == k


def largest_coefficient(N, m):
    c = [1]
    for _ in range(m):
        nc = [0] * (len(c) + N - 1)
        for i, a in enumerate(c):
            if a:
                for j in range(N):
                    nc[i + j] += a
        c = nc
    return max(c)


def check(d, say):
    ok = True
    why = []
    W = [int(x) for x in d["W"]]
    t = int(d["t"])
    if int(d["p"]) != P or W != W_PINNED:
        return False, ["the file's (p, W) are not the statement's (23, %s)" % W_PINNED]
    # 1. the tournament and t
    for a in W:
        for b in W:
            if a != b and arc(a, b) == arc(b, a):
                ok = False
                why.append("not a tournament")

    def transitive(sub):
        return any(all(arc(q[i], q[j]) for i in range(len(q)) for j in range(i + 1, len(q)))
                   for q in itertools.permutations(sub))

    if any(transitive(s) for s in itertools.combinations(W, t + 1)) or \
            not any(transitive(s) for s in itertools.combinations(W, t)):
        ok = False
        why.append("t(T7) != %d" % t)
    if t != T_PINNED:
        ok = False
        why.append("the file's t = %d is not the statement's 4" % t)
    say("1. T7 is a tournament; t(T7) = %d" % t)
    # 2. transitive cliques
    tr = {int(k): v for k, v in d["transitive_cliques"].items()}
    sym = {int(k): v for k, v in d["symmetric_cliques"].items()}
    if sorted(tr) != sorted(TR_PINNED) or sorted(sym) != sorted(SYM_PINNED):
        ok = False
        why.append("the listed powers are not the statement's")
    for n in sorted(tr):
        S = [tuple(int(x) for x in q) for q in tr[n]]
        if any(len(q) != n or any(x not in W for x in q) for q in S) or len(set(S)) != len(S):
            ok = False
            why.append("bad words in the transitive clique of power %d" % n)
            continue
        A = all(ordom(S[i], S[j]) for i in range(len(S)) for j in range(i + 1, len(S)))
        B1 = not any(sarc(S[j], S[i]) for i in range(len(S)) for j in range(i + 1, len(S)))
        B2 = kahn_acyclic(S)
        say("2. transitive clique of T7^%d: %d words; OR-forward %s; no backward strong arc %s; Kahn acyclic %s"
            % (n, len(S), A, B1, B2))
        if not (A and B1 and B2):
            ok = False
            why.append("the transitive clique of power %d fails" % n)
        if len(S) != TR_PINNED.get(n):
            ok = False
            why.append("the transitive clique of power %d has %d words, the statement says %s"
                       % (n, len(S), TR_PINNED.get(n)))
    # 3. symmetric cliques
    for n in sorted(sym):
        S = [tuple(int(x) for x in q) for q in sym[n]]
        if any(len(q) != n or any(x not in W for x in q) for q in S) or len(set(S)) != len(S):
            ok = False
            why.append("bad words in the symmetric clique of power %d" % n)
            continue
        good = all(ordom(u, v) for u in S for v in S if u != v)
        say("3. symmetric clique of T7^%d: %d words; every ordered pair has a forward coordinate %s"
            % (n, len(S), good))
        if not good:
            ok = False
            why.append("the symmetric clique of power %d fails" % n)
        if len(S) != SYM_PINNED.get(n):
            ok = False
            why.append("the symmetric clique of power %d has %d words, the statement says %s"
                       % (n, len(S), SYM_PINNED.get(n)))
    # 4. w(T7^2) = 7
    pts = [(a, b) for a in W for b in W]
    shared_two_way = [(u, v) for u in pts for v in pts
                      if u != v and (u[0] == v[0] or u[1] == v[1]) and ordom(u, v) and ordom(v, u)]
    graphs = []
    for s in itertools.permutations(W):
        G = [(x, s[i]) for i, x in enumerate(W)]
        if all(ordom(u, v) for u in G for v in G if u != v):
            graphs.append(sorted(G))
    listed = sorted(tuple(int(x) for x in q) for q in sym.get(2, []))
    unique = len(graphs) == 1 and graphs[0] == listed
    say("4. w(T7^2) <= 7: pairs of distinct points sharing a coordinate with OR-arcs both ways: %d; "
        "bijections of W whose graph is a symmetric clique: %d; it is the listed 7-set: %s"
        % (len(shared_two_way), len(graphs), unique))
    if shared_two_way or not unique:
        ok = False
        why.append("the w(T7^2) = 7 check fails")
    # 5. comparisons and the lift
    n2 = len(tr.get(2, []))
    n3 = len(tr.get(3, []))
    s3 = len(sym.get(3, []))
    s2 = len(sym.get(2, []))
    comp = (n2 > t ** 2, n3 ** 2 < n2 ** 3, s3 < t ** 3, s2 < t ** 2)
    if not all(comp):
        ok = False
        why.append("comparisons %s" % (comp,))
    m = 1
    while n2 > t * t and largest_coefficient(n2, m) <= (t * t) ** m:
        m += 1
        if m > 1000:
            break
    if m != LIFT_PINNED:
        ok = False
        why.append("the lift exponent is %d, the statement says 38" % m)
    say("5. %d > 16; %d^2 = %d < %d = %d^3 (the cube does not improve sqrt(%d)); %d < 64 and %d < 16; "
        "the largest coefficient of (1+...+x^%d)^%d exceeds 16^%d (more than 4^%d words in T7^%d)"
        % (n2, n3, n3 ** 2, n2 ** 3, n2, n2, s3, s2, n2 - 1, m, m, 2 * m, 2 * m))
    return ok, why


def safe(d, say):
    try:
        return check(d, say)
    except (KeyError, ValueError, TypeError, IndexError, AttributeError) as e:
        return False, ["malformed certificate: %r" % (e,)]


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "witnesses.json")) as fh:
        d = json.load(fh)
    ok, why = safe(d, print)
    if ok:
        print("PASS: tr(T7^2) >= 18, tr(T7^3) >= 75, w(T7^3) >= 16, w(T7^2) = 7; C(T7) >= sqrt(18)")
    else:
        print("FAIL: " + "; ".join(why[:4]))
    verdict = ok

    def forged(edit):
        f = json.loads(json.dumps(d))
        edit(f)
        return f

    def swap(f):
        o = f["transitive_cliques"]["2"]
        o[0], o[1] = o[1], o[0]

    def extra(f):
        f["symmetric_cliques"]["3"].append([0, 0, 0])

    def cut(f):
        f["transitive_cliques"]["2"] = f["transitive_cliques"]["2"][:16]

    def other_w(f):
        f["W"] = [0, 1, 2, 3, 9, 14, 19]

    for name, edit in (("the first two words of the square clique swapped", swap),
                       ("the word (0, 0, 0) added to the cube's symmetric clique", extra),
                       ("the square clique cut to 16 words", cut), ("vertex 18 replaced by 19", other_w)):
        fok, fwhy = safe(forged(edit), lambda s: None)
        print("control (%s): %s -- %s" % (name, "FAIL as expected" if not fok else "PASSED, which is wrong",
                                          "; ".join(fwhy[:2])))
        if fok:
            verdict = False
    print("VERDICT: PASS" if verdict else "VERDICT: FAIL")
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
