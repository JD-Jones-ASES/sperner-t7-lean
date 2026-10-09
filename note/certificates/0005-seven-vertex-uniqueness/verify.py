#!/usr/bin/env python3
"""Certificate 0005: on 7 vertices, T7 is the only tournament with C(T) > t(T), up to isomorphism.

T7 = Q23[W], W = {0, 1, 2, 3, 9, 14, 18}, x -> y iff y - x is a nonzero square mod 23. There are 456
isomorphism classes of tournaments on 7 vertices. Claim: 455 of them have C(T) = t(T), and the
remaining one is isomorphic to T7 (which has C(T7) > t(T7) = 4 by certificates 0001 and 0003 and by
the Lean theorem transitiveNumber_lt_capacity_T7). Two independent forms, each with its own
checker below; both must PASS.

  census_A.json (checker A): a list of 456 entries {arcs, t, scores, closed_gf2, M}. The
    relabellings of the entries are pairwise disjoint and cover all 2^21 labelled tournaments on
    7 vertices, so the list holds exactly one tournament per class; t by the score test (no
    transitive (t+1)-subset, a transitive t-subset); every entry with closed_gf2 has a 0/1 matrix
    with unit diagonal mod 2, zeros on the arcs and rank <= t over GF(2), so C(T) = t(T) by the
    rank lemma (capacity_le_of_factorization; see certificate 0004); exactly one entry is not
    closed, it has t = 4, and some relabelling maps it onto T7 (arcs rebuilt from the Paley rule).
  closure_B.json (checker B): {"classes": {n: [...]}} for n = 1..7, each class with a transitive
    witness and a proof of C(T) <= t(T) of one of three kinds: "degree" (Alon 1998, Theorem 1.2:
    C(T) <= min(max outdegree, max indegree) + 1), "delete" (C(T) <= C(T - v) + 1, with T - v
    matched to a listed class already proved at t - 1; see the lemma below), or "minrank" (a GF(p)
    matrix as above, of rank t). Classes are pairwise non-isomorphic (minimal arc code over all n!
    relabellings) and the orbit sums n!/|Aut| equal 2^(n choose 2). Exactly one 7-vertex class has
    kind "exceeds": its arcs must be T7's, rebuilt from the pinned W, and its 17 listed points of
    W x W must form a transitive clique of the second Sperner power (17 > 16 = t^2).

  The deletion lemma: group a clique of the m-th Sperner power of T by the set of coordinates
  holding v; within a group those coordinates agree, so the arcs lie elsewhere, and deleting them
  leaves a clique of a lower power of T - v; summing over the groups gives
  w(T^m) <= (C(T - v) + 1)^m.

A cross-check then matches the two 7-vertex lists class by class (same classes, same t, and the
exception of list A is the "exceeds" class of list B). Pinned here: W, t(T7) = 4, the class counts
1, 1, 2, 4, 12, 56, 456, and exactly one exception.

Standard library only; exact integers; no assert statements. Forged controls run automatically
(each must FAIL): for form A, a matrix entry moved onto an arc, one class dropped, and the T7 entry
marked closed with the identity matrix (rank 7, not 4); for form B, the 17 points in
reverse order, a minrank matrix row set to all ones, the T7 class dropped, and the exceeds data
pointing at another 7-subset of Q23. The run takes about a minute. The last line is VERDICT: PASS
or VERDICT: FAIL; the exit status is 0 only on PASS.

Usage: python -O verify.py      (reads census_A.json and closure_B.json next to this file)
"""
import itertools
import json
import math
import os
import sys

P = 23
W_PINNED = [0, 1, 2, 3, 9, 14, 18]
T_T7 = 4
COUNTS = {1: 1, 2: 1, 3: 2, 4: 4, 5: 12, 6: 56, 7: 456}
SQ = {(x * x) % P for x in range(1, P)}
T7_ARCS = {(i, j) for i in range(7) for j in range(7) if i != j and ((W_PINNED[j] - W_PINNED[i]) % P) in SQ}
PAIRS7 = list(itertools.combinations(range(7), 2))
PERMS7 = list(itertools.permutations(range(7)))


# ----------------------------------------------------------------------------------------------
# Checker A (ported from the bench lane that built census_A.json)
# ----------------------------------------------------------------------------------------------

def a_rank2(M):
    rows = [int("".join(str(x % 2) for x in r), 2) for r in M]
    r = 0
    for bit in reversed(range(7)):
        piv = next((i for i in range(r, 7) if rows[i] >> bit & 1), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(7):
            if i != r and rows[i] >> bit & 1:
                rows[i] ^= rows[r]
        r += 1
    return r


def check_A(data, say):
    """Return (ok, reasons, owner) where owner[code] = 1 + index of the entry covering that code."""
    ok = True
    why = []
    owner = [0] * (1 << 21)
    ncov = 0
    unclosed = []
    for idx, d in enumerate(data):
        arcs = set(tuple(a) for a in d["arcs"])
        A = [[(i, j) in arcs for j in range(7)] for i in range(7)]
        if any(A[i][i] for i in range(7)) or any(A[i][j] == A[j][i] for i, j in PAIRS7):
            ok = False
            why.append("entry %d is not a tournament" % idx)
            continue
        mine = set()
        for pm in PERMS7:
            c = 0
            for e, (i, j) in enumerate(PAIRS7):
                if A[pm[i]][pm[j]]:
                    c |= 1 << e
            mine.add(c)
        clash = False
        for c in mine:
            if owner[c]:
                if not clash:
                    ok = False
                    why.append("entry %d is isomorphic to entry %d" % (idx, owner[c] - 1))
                    clash = True
                continue
            owner[c] = idx + 1
            ncov += 1
        t = int(d["t"])

        def trans(s):
            return sorted(sum(A[a][b] for b in s) for a in s) == list(range(len(s)))

        if t < 1 or t > 7 or (t < 7 and any(trans(s) for s in itertools.combinations(range(7), t + 1))) \
                or not any(trans(s) for s in itertools.combinations(range(7), t)):
            ok = False
            why.append("entry %d: t is wrong" % idx)
        if d["closed_gf2"]:
            M = d["M"]
            if (M is None or len(M) != 7 or any(len(r) != 7 for r in M)
                    or any(M[i][i] % 2 == 0 for i in range(7))
                    or any(A[i][j] and M[i][j] % 2 for i in range(7) for j in range(7))
                    or a_rank2(M) > t):
                ok = False
                why.append("entry %d: the matrix fails" % idx)
        else:
            unclosed.append((idx, A, t))
    say("  A: %d entries; relabellings cover %d of %d labelled tournaments" % (len(data), ncov, 1 << 21))
    if ncov != 1 << 21 or len(data) != COUNTS[7]:
        ok = False
        why.append("not one entry per class")
    exception = None
    if len(unclosed) != 1:
        ok = False
        why.append("%d entries are not closed, exactly one expected" % len(unclosed))
    else:
        idx, A, t = unclosed[0]
        iso = next((pm for pm in PERMS7
                    if all(A[pm[i]][pm[j]] == ((i, j) in T7_ARCS) for i in range(7) for j in range(7) if i != j)),
                   None)
        say("  A: the one entry not closed (%d) has t = %d; isomorphic to T7: %s%s"
            % (idx, t, iso is not None, "" if iso is None else " (vertex %s of T7 is vertex %s of the entry)"
               % (W_PINNED, list(iso))))
        if iso is None or t != T_T7:
            ok = False
            why.append("the entry not closed is not T7")
        else:
            exception = idx
    return ok, why, (owner, exception)


# ----------------------------------------------------------------------------------------------
# Checker B (ported from the second bench lane, which built closure_B.json independently)
# ----------------------------------------------------------------------------------------------

def b_is_prime(p):
    return isinstance(p, int) and p >= 2 and all(p % d for d in range(2, int(p ** 0.5) + 1))


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

    def fail(msg):
        nonlocal ok
        ok = False
        why.append(msg)

    C = cert.get("classes", {})
    proven = {}
    canon_of = {}
    exceeders = []
    for n in range(1, 8):
        lst = C.get(str(n))
        if not isinstance(lst, list):
            fail("no class list for n = %d" % n)
            continue
        orbit_sum = 0
        for rec in lst:
            cid = rec.get("id")
            A = b_build(n, rec.get("arcs", []))
            if A is None:
                fail("%s: not a tournament on %d vertices" % (cid, n))
                continue
            cc, aut = b_canon_aut(A)
            if (n, cc) in canon_of:
                fail("%s: isomorphic to %s" % (cid, canon_of[(n, cc)]))
                continue
            canon_of[(n, cc)] = cid
            orbit_sum += math.factorial(n) // aut
            Wt = rec.get("witness", [])
            if (not isinstance(Wt, list) or len(set(Wt)) != len(Wt)
                    or any(not (isinstance(x, int) and 0 <= x < n) for x in Wt)):
                fail("%s: malformed witness" % cid)
                continue
            if any(not A[Wt[i]][Wt[j]] for i in range(len(Wt)) for j in range(i + 1, len(Wt))):
                fail("%s: the witness is not transitive in the listed order" % cid)
                continue
            k = len(Wt)
            te = b_t_exact(A)
            if te != k:
                fail("%s: exhaustive t = %d, witness size %d" % (cid, te, k))
                continue
            pr = rec.get("proof", {})
            kind = pr.get("kind")
            good = False
            if kind == "degree":
                mo = max(sum(A[u]) for u in range(n))
                mi = max(sum(A[u][v] for u in range(n)) for v in range(n))
                good = (min(mo, mi) + 1 == k)
                if not good:
                    fail("%s: degree bound %d != %d" % (cid, min(mo, mi) + 1, k))
            elif kind == "delete":
                v = pr.get("v")
                sid = pr.get("sub")
                if not (isinstance(v, int) and 0 <= v < n) or n < 2:
                    fail("%s: bad deleted vertex" % cid)
                else:
                    keep = [u for u in range(n) if u != v]
                    Bm = [[A[a][b] for b in keep] for a in keep]
                    cb, _ = b_canon_aut(Bm)
                    if canon_of.get((n - 1, cb)) != sid:
                        fail("%s: T - %d is not class %s" % (cid, v, sid))
                    elif proven.get(sid) != k - 1:
                        fail("%s: class %s is not proved at value %d" % (cid, sid, k - 1))
                    else:
                        good = True
            elif kind == "minrank":
                p = pr.get("p")
                M = pr.get("M")
                if not b_is_prime(p):
                    fail("%s: p is not prime" % cid)
                elif (not isinstance(M, list) or len(M) != n
                      or any(not isinstance(r, list) or len(r) != n for r in M)
                      or any(not isinstance(x, int) for r in M for x in r)):
                    fail("%s: malformed matrix" % cid)
                else:
                    bad = [(u, v) for u in range(n) for v in range(n) if A[u][v] and M[u][v] % p]
                    zd = [v for v in range(n) if M[v][v] % p == 0]
                    if bad:
                        fail("%s: matrix nonzero on arcs %s" % (cid, bad))
                    elif zd:
                        fail("%s: zero diagonal at %s" % (cid, zd))
                    else:
                        rk = b_rank_gfp(M, p)
                        if rk != k:
                            fail("%s: rank %d over GF(%d) != %d" % (cid, rk, p, k))
                        else:
                            good = True
            elif kind == "exceeds":
                Wq = pr.get("W")
                order = pr.get("order")
                if n != 7 or Wq != W_PINNED:
                    fail("%s: the exceeds data must name W = %s on 7 vertices" % (cid, W_PINNED))
                elif any(A[i][j] != (1 if (i, j) in T7_ARCS else 0) for i in range(7) for j in range(7)):
                    fail("%s: the arcs are not those of T7 = Q23[W]" % cid)
                elif k != T_T7:
                    fail("%s: t = %d, not 4" % (cid, k))
                elif (not isinstance(order, list) or any(not (isinstance(p_, list) and len(p_) == 2
                       and all(isinstance(x, int) and 0 <= x < 7 for x in p_)) for p_ in order)
                       or len(set(map(tuple, order))) != len(order)):
                    fail("%s: malformed point list" % cid)
                else:
                    bad = [(i, j) for i in range(len(order)) for j in range(i + 1, len(order))
                           if not any(A[order[i][c]][order[j][c]] for c in range(2))]
                    if bad:
                        fail("%s: the order fails at pairs %s" % (cid, bad[:3]))
                    elif not len(order) > k * k:
                        fail("%s: %d points do not exceed t^2 = %d" % (cid, len(order), k * k))
                    else:
                        exceeders.append(cid)
            else:
                fail("%s: unknown proof kind %s" % (cid, kind))
            if good:
                proven[cid] = k
        total = 2 ** (n * (n - 1) // 2)
        if orbit_sum != total:
            fail("n = %d: orbit sum %d != %d (class list incomplete)" % (n, orbit_sum, total))
        nprov = sum(1 for rec in lst if rec.get("id") in proven)
        say("  B: n = %d: %d classes, orbit sum %d of %d, C = t proven for %d" % (n, len(lst), orbit_sum, total, nprov))
        want = COUNTS[n] - (1 if n == 7 else 0)
        if len(lst) != COUNTS[n] or nprov != want:
            fail("n = %d: %d of %d classes proven, %d required (%d classes expected)"
                 % (n, nprov, len(lst), want, COUNTS[n]))
    if len(exceeders) != 1:
        fail("exceeding classes verified: %s (exactly one required)" % exceeders)
    else:
        say("  B: the one class not closed, %s, is T7 = Q23[W] with t = 4 and a 17-point transitive clique "
            "of its second Sperner power" % exceeders[0])
    return ok, why, exceeders


# ----------------------------------------------------------------------------------------------
# Cross-check and driver
# ----------------------------------------------------------------------------------------------

def cross(dataA, ownerA, excA, certB):
    hits = 0
    for rec in certB["classes"]["7"]:
        A = b_build(7, rec["arcs"])
        code = b_code_under(A, list(range(7)))
        e = ownerA[code] - 1
        if e < 0:
            return False, "class %s of list B is not covered by list A" % rec["id"]
        if int(dataA[e]["t"]) != len(rec["witness"]):
            return False, "class %s: t = %d in list B, %s in list A" % (rec["id"], len(rec["witness"]), dataA[e]["t"])
        if (rec["proof"]["kind"] == "exceeds") != (e == excA):
            return False, "class %s: the exceptions of the two lists differ" % rec["id"]
        hits += 1
    if hits != COUNTS[7] or len(set(ownerA[b_code_under(b_build(7, r["arcs"]), list(range(7)))]
                                    for r in certB["classes"]["7"])) != COUNTS[7]:
        return False, "the two 7-vertex lists do not match one to one"
    return True, "the two lists hold the same 456 classes with the same t and the same exception"


def safe(fn, *args):
    try:
        return fn(*args)
    except (KeyError, ValueError, TypeError, IndexError, AttributeError) as e:
        return False, ["malformed certificate: %r" % (e,)], None


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "census_A.json")) as fh:
        dataA = json.load(fh)
    with open(os.path.join(here, "closure_B.json")) as fh:
        certB = json.load(fh)
    okA, whyA, extraA = safe(check_A, dataA, print)
    print(("PASS" if okA else "FAIL") + " (checker A, census_A.json)" + ("" if okA else ": " + "; ".join(whyA[:4])))
    okB, whyB, _ = safe(check_B, certB, print)
    print(("PASS" if okB else "FAIL") + " (checker B, closure_B.json)" + ("" if okB else ": " + "; ".join(whyB[:4])))
    if okA and okB:
        okX, msgX = cross(dataA, extraA[0], extraA[1], certB)
    else:
        okX, msgX = False, "skipped"
    print(("PASS" if okX else "FAIL") + " (cross-check): " + msgX)
    verdict = okA and okB and okX
    if verdict:
        print("PASS: 455 of the 456 tournaments on 7 vertices have C(T) = t(T); the remaining class is T7")

    def fA(edit):
        f = json.loads(json.dumps(dataA))
        edit(f)
        return f

    def fB(edit):
        f = json.loads(json.dumps(certB))
        edit(f)
        return f

    def a_on_arc(f):
        e = [d for d in f if d["closed_gf2"]][100]
        u, v = e["arcs"][0]
        e["M"][u][v] = 1

    def a_drop(f):
        f.pop(200)

    def a_t7_closed(f):
        e = [d for d in f if not d["closed_gf2"]][0]
        e["closed_gf2"] = True
        e["M"] = [[1 if i == j else 0 for j in range(7)] for i in range(7)]

    def b_reverse(f):
        r = [x for x in f["classes"]["7"] if x["proof"]["kind"] == "exceeds"][0]
        r["proof"]["order"] = list(reversed(r["proof"]["order"]))

    def b_ones(f):
        r = [x for x in f["classes"]["7"] if x["proof"]["kind"] == "minrank"][0]
        r["proof"]["M"][0] = [1] * 7

    def b_drop_t7(f):
        f["classes"]["7"] = [x for x in f["classes"]["7"] if x["proof"]["kind"] != "exceeds"]

    def b_other_w(f):
        r = [x for x in f["classes"]["7"] if x["proof"]["kind"] == "exceeds"][0]
        r["proof"]["W"] = [0, 1, 2, 3, 9, 14, 19]

    quiet = lambda s: None
    controls = [("A: a matrix entry moved onto an arc", check_A, fA(a_on_arc)),
                ("A: one class dropped", check_A, fA(a_drop)),
                ("A: the T7 entry marked closed with the identity matrix", check_A, fA(a_t7_closed)),
                ("B: the 17 points in reverse order", check_B, fB(b_reverse)),
                ("B: a minrank matrix row set to all ones", check_B, fB(b_ones)),
                ("B: the T7 class dropped", check_B, fB(b_drop_t7)),
                ("B: the exceeds data naming another 7-subset of Q23", check_B, fB(b_other_w))]
    for name, fn, data in controls:
        fok, fwhy, _ = safe(fn, data, quiet)
        print("control (%s): %s -- %s" % (name, "FAIL as expected" if not fok else "PASSED, which is wrong",
                                          "; ".join(fwhy[:2])))
        if fok:
            verdict = False
    print("VERDICT: PASS" if verdict else "VERDICT: FAIL")
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
