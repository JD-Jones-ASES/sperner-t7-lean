#!/usr/bin/env python3
"""Certificate 0004: every tournament on at most 6 vertices has C(T) = t(T).

The rank lemma (the theorem capacity_le_of_factorization of this repository, in matrix form): if
M is a V x V matrix over a field with M[v][v] != 0 for every vertex and M[u][v] = 0 for every arc
u -> v, then C(T) <= rank M. A clique of the n-th Sperner power indexes a nonsingular diagonal
block of the n-th Kronecker power of M, and a matrix of rank r factors through F^r. Since
t(T) <= C(T) always, a matrix of rank t(T) gives C(T) = t(T).

The certificate lists, for every n = 1..6, one tournament from each isomorphism class (1, 1, 2, 4,
12 and 56 classes) with its transitive number t and a 0/1 matrix over GF(2) of rank t with that
pattern. It comes in two independent forms, each with its own checker below; both must PASS.

  classes_A.json (checker A): a list of {k, arcs, t, p, M}. For each n the relabellings of the
    listed classes are pairwise disjoint and cover all 2^(n choose 2) labelled tournaments, so the
    list holds exactly one tournament per class. t by the score test and by an ordering search
    (no transitive (t+1)-subset, a transitive t-subset). M: nonzero diagonal mod 2, zero at every
    arc, rank <= t by elimination mod 2, and every (t+1) x (t+1) minor is 0 mod 2 (Leibniz).
  classes_B.json (checker B): {"classes": {n: [{id, arcs, witness, proof: {kind, p, M}}]}}.
    For each n the classes are pairwise non-isomorphic (minimal arc code over all n! relabellings)
    and the orbit sum of n!/|Aut| equals 2^(n choose 2), so every labelled tournament is
    isomorphic to exactly one listed class; the witness is transitive in the listed order and t is
    its size by an exhaustive search; the matrix has nonzero diagonal mod 2, zeros on the arcs and
    rank exactly t over GF(2) by elimination.

A cross-check then matches the two lists class by class (same classes, same t). The statement
constants are pinned here: n = 1..6, the class counts 1, 1, 2, 4, 12, 56, and p = 2.

Standard library only; exact integers; no assert statements. Forged controls run automatically
(each must FAIL): for each form, a matrix entry moved onto an arc, a 6-vertex class dropped, and a
wrong t or witness; for form A also a class listed twice; for form B also the matrix of T6_55
replaced by the identity. The last line is VERDICT: PASS or VERDICT: FAIL; the exit status is 0
only on PASS.

Usage: python -O verify.py      (reads classes_A.json and classes_B.json next to this file)
"""
import itertools
import json
import math
import os
import sys

COUNTS = {1: 1, 2: 1, 3: 2, 4: 4, 5: 12, 6: 56}
PRIME = 2


# ----------------------------------------------------------------------------------------------
# Checker A (ported from the bench lane that built classes_A.json)
# ----------------------------------------------------------------------------------------------

def a_perm_sign(p):
    p = list(p)
    s = 1
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]
            p[i], p[j] = p[j], p[i]
            s = -s
    return s


def a_det(R):
    tot = 0
    for pm in itertools.permutations(range(len(R))):
        pr = 1
        for i in range(len(R)):
            pr *= R[i][pm[i]]
            if not pr:
                break
        tot += a_perm_sign(pm) * pr
    return tot


def a_rank_mod(M, p):
    R = [[x % p for x in row] for row in M]
    r = 0
    n = len(R)
    for c in range(n):
        piv = next((i for i in range(r, n) if R[i][c]), None)
        if piv is None:
            continue
        R[r], R[piv] = R[piv], R[r]
        iv = pow(R[r][c], p - 2, p)
        R[r] = [(x * iv) % p for x in R[r]]
        for i in range(n):
            if i != r and R[i][c]:
                f = R[i][c]
                R[i] = [(x - f * y) % p for x, y in zip(R[i], R[r])]
        r += 1
    return r


def a_codes(k, arcs):
    pairs = list(itertools.combinations(range(k), 2))
    A = [[(i, j) in arcs for j in range(k)] for i in range(k)]
    return {tuple(A[pm[i]][pm[j]] for i, j in pairs) for pm in itertools.permutations(range(k))}


def check_A(data, say):
    ok = True
    why = []
    for k in range(1, 7):
        ents = [d for d in data if d["k"] == k]
        pairs = list(itertools.combinations(range(k), 2))
        cover = {}
        for idx, d in enumerate(ents):
            arcs = set(tuple(a) for a in d["arcs"])
            A = [[(i, j) in arcs for j in range(k)] for i in range(k)]
            if any(A[i][i] for i in range(k)) or any(A[i][j] == A[j][i] for i, j in pairs) or \
                    any(not (0 <= a < k and 0 <= b < k) for a, b in arcs):
                ok = False
                why.append("k=%d entry %d is not a tournament" % (k, idx))
                continue
            clash = False
            for c in a_codes(k, arcs):
                if c in cover and not clash:
                    ok = False
                    why.append("k=%d entries %d and %d are isomorphic" % (k, cover[c], idx))
                    clash = True
                cover.setdefault(c, idx)
            t = int(d["t"])

            def trans(s):
                return sorted(sum(A[a][b] for b in s) for a in s) == list(range(len(s)))

            def trans2(s):
                return any(all(A[q[i]][q[j]] for i in range(len(q)) for j in range(i + 1, len(q)))
                           for q in itertools.permutations(s))

            big = list(itertools.combinations(range(k), t + 1)) if t < k else []
            if t < 1 or t > k or any(trans(s) or trans2(s) for s in big):
                ok = False
                why.append("k=%d entry %d has a transitive %d-set" % (k, idx, t + 1))
            if not any(trans(s) and trans2(s) for s in itertools.combinations(range(k), t)):
                ok = False
                why.append("k=%d entry %d has no transitive %d-set" % (k, idx, t))
            p = d["p"]
            M = d["M"]
            if p != PRIME or M is None or len(M) != k or any(len(r) != k for r in M):
                ok = False
                why.append("k=%d entry %d: no GF(2) matrix" % (k, idx))
                continue
            for i in range(k):
                if M[i][i] % p == 0:
                    ok = False
                    why.append("k=%d entry %d: zero diagonal at %d" % (k, idx, i))
                for j in range(k):
                    if A[i][j] and M[i][j] % p:
                        ok = False
                        why.append("k=%d entry %d: nonzero at arc %d->%d" % (k, idx, i, j))
            if a_rank_mod(M, p) > t:
                ok = False
                why.append("k=%d entry %d: rank %d > t = %d" % (k, idx, a_rank_mod(M, p), t))
            if t < k:
                bad_minor = False
                for rs in itertools.combinations(range(k), t + 1):
                    for cs in itertools.combinations(range(k), t + 1):
                        if a_det([[M[i][j] for j in cs] for i in rs]) % p:
                            bad_minor = True
                            break
                    if bad_minor:
                        break
                if bad_minor:
                    ok = False
                    why.append("k=%d entry %d: a nonzero (t+1)-minor mod 2" % (k, idx))
        allcodes = 1 << len(pairs)
        say("  A: n = %d: %d classes listed (%d expected); relabellings cover %d of %d labelled tournaments"
            % (k, len(ents), COUNTS[k], len(cover), allcodes))
        if len(cover) != allcodes or len(ents) != COUNTS[k]:
            ok = False
            why.append("n=%d: the list is not one tournament per class" % k)
    if len(data) != sum(COUNTS.values()):
        ok = False
        why.append("%d entries, %d expected" % (len(data), sum(COUNTS.values())))
    return ok, why


# ----------------------------------------------------------------------------------------------
# Checker B (ported from the second bench lane, which built classes_B.json independently)
# ----------------------------------------------------------------------------------------------

def b_build(n, arcs):
    A = [[0] * n for _ in range(n)]
    for e in arcs:
        if not (isinstance(e, list) and len(e) == 2):
            return None
        u, v = e
        if not (isinstance(u, int) and isinstance(v, int) and 0 <= u < n and 0 <= v < n and u != v):
            return None
        if A[u][v]:
            return None
        A[u][v] = 1
    for u in range(n):
        for v in range(u + 1, n):
            if A[u][v] + A[v][u] != 1:
                return None
    return A


def b_code_under(A, q):
    n = len(A)
    c = 0
    k = 0
    for a in range(n):
        for b in range(a + 1, n):
            if A[q[a]][q[b]]:
                c |= 1 << k
            k += 1
    return c


def b_canon_aut(A):
    best = None
    aut = 0
    for q in itertools.permutations(range(len(A))):
        c = b_code_under(A, q)
        if best is None or c < best:
            best, aut = c, 1
        elif c == best:
            aut += 1
    return best, aut


def b_t_exact(A):
    n = len(A)
    best = 0
    for m in range(1, 1 << n):
        S = [i for i in range(n) if (m >> i) & 1]
        if len(S) <= best:
            continue
        if sorted(sum(A[x][y] for y in S) for x in S) == list(range(len(S))):
            best = len(S)
    return best


def b_rank_gfp(M, p):
    M = [[x % p for x in row] for row in M]
    rows, cols = len(M), len(M[0]) if M else 0
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c]:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(x - f * y) % p for x, y in zip(M[i], M[r])]
        r += 1
    return r


def check_B(cert, say):
    ok = True
    why = []
    C = cert.get("classes", {})
    if sorted(C.keys()) != [str(n) for n in range(1, 7)]:
        ok = False
        why.append("class lists for n = %s, expected 1..6" % sorted(C.keys()))
    for n in range(1, 7):
        lst = C.get(str(n))
        if not isinstance(lst, list):
            ok = False
            why.append("no class list for n = %d" % n)
            continue
        seen = {}
        orbit_sum = 0
        proven = 0
        for rec in lst:
            cid = rec.get("id")
            A = b_build(n, rec.get("arcs", []))
            if A is None:
                ok = False
                why.append("%s: not a tournament on %d vertices" % (cid, n))
                continue
            cc, aut = b_canon_aut(A)
            if cc in seen:
                ok = False
                why.append("%s: isomorphic to %s" % (cid, seen[cc]))
                continue
            seen[cc] = cid
            orbit_sum += math.factorial(n) // aut
            Wt = rec.get("witness", [])
            if (not isinstance(Wt, list) or len(set(Wt)) != len(Wt)
                    or any(not (isinstance(x, int) and 0 <= x < n) for x in Wt)):
                ok = False
                why.append("%s: malformed witness" % cid)
                continue
            if any(not A[Wt[i]][Wt[j]] for i in range(len(Wt)) for j in range(i + 1, len(Wt))):
                ok = False
                why.append("%s: the witness is not transitive in the listed order" % cid)
                continue
            k = len(Wt)
            te = b_t_exact(A)
            if te != k:
                ok = False
                why.append("%s: exhaustive t = %d, witness size %d" % (cid, te, k))
                continue
            pr = rec.get("proof", {})
            p = pr.get("p")
            M = pr.get("M")
            if pr.get("kind") != "minrank" or p != PRIME:
                ok = False
                why.append("%s: not a GF(2) rank proof" % cid)
                continue
            if (not isinstance(M, list) or len(M) != n
                    or any(not isinstance(r, list) or len(r) != n for r in M)
                    or any(not isinstance(x, int) for r in M for x in r)):
                ok = False
                why.append("%s: malformed matrix" % cid)
                continue
            bad = [(u, v) for u in range(n) for v in range(n) if A[u][v] and M[u][v] % p]
            zd = [v for v in range(n) if M[v][v] % p == 0]
            if bad:
                ok = False
                why.append("%s: matrix nonzero on arcs %s" % (cid, bad))
                continue
            if zd:
                ok = False
                why.append("%s: zero diagonal at %s" % (cid, zd))
                continue
            rk = b_rank_gfp(M, p)
            if rk != k:
                ok = False
                why.append("%s: rank %d over GF(2), t = %d" % (cid, rk, k))
                continue
            proven += 1
        total = 2 ** (n * (n - 1) // 2)
        say("  B: n = %d: %d classes, orbit sum %d of %d, C = t proven for %d"
            % (n, len(lst), orbit_sum, total, proven))
        if orbit_sum != total:
            ok = False
            why.append("n = %d: orbit sum %d != %d (class list incomplete)" % (n, orbit_sum, total))
        if len(lst) != COUNTS[n] or proven != len(lst):
            ok = False
            why.append("n = %d: %d of %d classes proven, %d classes expected" % (n, proven, len(lst), COUNTS[n]))
    return ok, why


# ----------------------------------------------------------------------------------------------
# Cross-check and driver
# ----------------------------------------------------------------------------------------------

def cross(dataA, certB):
    """The two lists name the same classes with the same t."""
    index = {}
    for d in dataA:
        arcs = set(tuple(a) for a in d["arcs"])
        for c in a_codes(d["k"], arcs):
            index[(d["k"], c)] = int(d["t"])
    for n in range(1, 7):
        for rec in certB["classes"][str(n)]:
            arcs = set(tuple(a) for a in rec["arcs"])
            pairs = list(itertools.combinations(range(n), 2))
            code = tuple((i, j) in arcs for i, j in pairs)
            if index.get((n, code)) != len(rec["witness"]):
                return False, "class %s of list B has t = %d; list A gives %s" % (
                    rec["id"], len(rec["witness"]), index.get((n, code)))
    return True, "both lists hold the same %d classes with the same t" % sum(COUNTS.values())


def safe(fn, *args):
    try:
        return fn(*args)
    except (KeyError, ValueError, TypeError, IndexError, AttributeError) as e:
        return False, ["malformed certificate: %r" % (e,)]


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "classes_A.json")) as fh:
        dataA = json.load(fh)
    with open(os.path.join(here, "classes_B.json")) as fh:
        certB = json.load(fh)
    verdict = True
    okA, whyA = safe(check_A, dataA, print)
    print(("PASS" if okA else "FAIL") + " (checker A, classes_A.json)" + ("" if okA else ": " + "; ".join(whyA[:4])))
    okB, whyB = safe(check_B, certB, print)
    print(("PASS" if okB else "FAIL") + " (checker B, classes_B.json)" + ("" if okB else ": " + "; ".join(whyB[:4])))
    okX, msgX = (False, "skipped") if not (okA and okB) else cross(dataA, certB)
    print(("PASS" if okX else "FAIL") + " (cross-check): " + msgX)
    verdict = okA and okB and okX
    if verdict:
        print("PASS: every tournament on at most 6 vertices has a GF(2) matrix of rank t(T) with nonzero "
              "diagonal and zeros on the arcs, so C(T) = t(T)")

    def fA(edit):
        f = json.loads(json.dumps(dataA))
        edit(f)
        return f

    def fB(edit):
        f = json.loads(json.dumps(certB))
        edit(f)
        return f

    def a_on_arc(f):
        e = [d for d in f if d["k"] == 6][10]
        u, v = e["arcs"][0]
        e["M"][u][v] = 1

    def a_drop(f):
        f.remove([d for d in f if d["k"] == 6][20])

    def a_t(f):
        e = [d for d in f if d["k"] == 6 and d["t"] == 4][0]
        e["t"] = 3

    def a_twice(f):
        six = [i for i, d in enumerate(f) if d["k"] == 6]
        f[six[1]] = json.loads(json.dumps(f[six[0]]))

    def b_on_arc(f):
        r = [x for x in f["classes"]["6"] if x["id"] == "T6_25"][0]
        u, v = r["arcs"][0]
        r["proof"]["M"][u][v] = 1

    def b_drop(f):
        f["classes"]["6"].pop(30)

    def b_witness(f):
        r = [x for x in f["classes"]["6"] if x["id"] == "T6_55"][0]
        r["witness"] = r["witness"] + [v for v in range(6) if v not in r["witness"]][:1]

    def b_identity(f):
        r = [x for x in f["classes"]["6"] if x["id"] == "T6_55"][0]
        r["proof"]["M"] = [[1 if i == j else 0 for j in range(6)] for i in range(6)]

    quiet = lambda s: None
    controls = [("A: a matrix entry moved onto an arc", check_A, fA(a_on_arc)),
                ("A: one 6-vertex class dropped", check_A, fA(a_drop)),
                ("A: t claimed one smaller", check_A, fA(a_t)),
                ("A: a class listed twice", check_A, fA(a_twice)),
                ("B: a matrix entry moved onto an arc", check_B, fB(b_on_arc)),
                ("B: one 6-vertex class dropped", check_B, fB(b_drop)),
                ("B: a non-transitive witness for T6_55", check_B, fB(b_witness)),
                ("B: the matrix of T6_55 replaced by the identity", check_B, fB(b_identity))]
    for name, fn, data in controls:
        fok, fwhy = safe(fn, data, quiet)
        print("control (%s): %s -- %s" % (name, "FAIL as expected" if not fok else "PASSED, which is wrong",
                                          "; ".join(fwhy[:2])))
        if fok:
            verdict = False
    print("VERDICT: PASS" if verdict else "VERDICT: FAIL")
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
