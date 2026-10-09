#!/usr/bin/env python3
"""Certificate 0006: C(T7) <= 5, by a rank-5 matrix with nonzero diagonal and zeros on the arcs.

T7 = Q23[W], W = {0, 1, 2, 3, 9, 14, 18}, x -> y iff y - x is a nonzero square mod 23.

The rank lemma (the theorem capacity_le_of_factorization of this repository): let F be a field and
M = A B a V x V matrix over F that factors through F^r, with M[v][v] != 0 for every vertex and
M[u][v] = 0 for every arc u -> v. For words u, v of length n put K[u][v] = prod_i M[u_i][v_i], the
n-th Kronecker power of M, which factors through F^(r^n). If some coordinate of u carries an arc
to v, then K[u][v] = 0, and K[u][u] != 0. So a clique of the n-th Sperner power indexes a
diagonal block of K with nonzero diagonal (a transitive clique, in its order, a triangular one),
and its size is at most r^n. Hence C(T7) <= r.

Standard library only; exact integers; no assert statements. Reads rank_certificate.json next to
this file. The statement constants are pinned here: p = 23, W, the rank 5, and the Lean factors
T7A and T7B (rows in the W order). Checks:

  1. T7 is a tournament with 21 arcs, rebuilt from the Paley rule.
  2. The integer matrix M (over Q): nonzero diagonal, zero at every arc.
  3. rank M over Q is 5, two routes: Fraction elimination; every 6 x 6 minor is 0 and some 5 x 5
     minor is nonzero (Leibniz, exact integers).
  4. The factorization used in Lean, over GF(2): A is 7 x 5 and B is 5 x 7, both equal to the
     pinned T7A and T7B; A B mod 2 has 1 on the diagonal and 0 at every arc; and A B equals M mod 2
     entrywise (so the GF(2) reduction of M has rank at most 5, and the rank-5 claim over Q and the
     Lean factorization describe the same matrix).
  5. A demonstration of the lemma on the 18-point transitive clique of certificate 0003: the
     18 x 18 block of M (x) M, in the listed order, is triangular with diagonal entries +-1 (over
     Q) and 1 (over GF(2) through A B); 18 <= 25.

Forged controls run automatically (each must FAIL): an entry put on the arc 0 -> 1; the last
diagonal entry changed to 2 (rank 6 over Q, and zero mod 2); the rank claimed to be 4; one bit
of A flipped; a vertex of W replaced. The last line is VERDICT: PASS or VERDICT: FAIL; the exit
status is 0 only on PASS.

Usage: python -O verify.py
"""
import itertools
import json
import os
import sys
from fractions import Fraction

P = 23
W_PINNED = [0, 1, 2, 3, 9, 14, 18]
R_PINNED = 5
A_LEAN = ["10000", "01000", "00100", "00010", "01110", "00001", "01100"]
B_LEAN = ["1000000", "0100001", "0110100", "0011001", "0000010"]
SQ = {(x * x) % P for x in range(1, P)}


def arc(a, b):
    return a != b and ((b - a) % P) in SQ


def sign(perm):
    s = 1
    p = list(perm)
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]
            p[i], p[j] = p[j], p[i]
            s = -s
    return s


def det(rows):
    k = len(rows)
    tot = 0
    for perm in itertools.permutations(range(k)):
        prod = 1
        for i in range(k):
            prod *= rows[i][perm[i]]
            if prod == 0:
                break
        if prod:
            tot += sign(perm) * prod
    return tot


def rank_q(M):
    R = [[Fraction(x) for x in row] for row in M]
    n, m = len(R), len(R[0])
    r = 0
    for c in range(m):
        piv = None
        for i in range(r, n):
            if R[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        R[r], R[piv] = R[piv], R[r]
        for i in range(n):
            if i != r and R[i][c] != 0:
                f = R[i][c] / R[r][c]
                R[i] = [x - f * y for x, y in zip(R[i], R[r])]
        r += 1
    return r


def check(d, say):
    ok = True
    why = []
    W = [int(x) for x in d["W"]]
    M = [[int(x) for x in row] for row in d["M"]]
    r = int(d["rank"])
    n = len(W)
    if int(d["p"]) != P or W != W_PINNED:
        return False, ["the file's (p, W) are not the statement's (23, %s)" % W_PINNED]
    if len(M) != n or any(len(row) != n for row in M):
        return False, ["M is not %d x %d" % (n, n)]
    # 1. the tournament
    for a in W:
        for b in W:
            if a != b and arc(a, b) == arc(b, a):
                ok = False
                why.append("not a tournament at %d, %d" % (a, b))
    narcs = sum(1 for a in W for b in W if arc(a, b))
    if narcs != 21:
        ok = False
        why.append("%d arcs, not 21" % narcs)
    say("1. T7 = Q23[%s] is a tournament with %d arcs" % (W, narcs))
    # 2. the pattern over Q
    for i in range(n):
        if M[i][i] == 0:
            ok = False
            why.append("zero diagonal at %d" % W[i])
        for j in range(n):
            if arc(W[i], W[j]) and M[i][j] != 0:
                ok = False
                why.append("nonzero entry at the arc %d -> %d" % (W[i], W[j]))
    say("2. M: nonzero diagonal and zeros on the arcs: %s" % ok)
    # 3. the rank over Q, two routes
    rq = rank_q(M)
    if rq != r:
        ok = False
        why.append("rank over Q by elimination is %d, claimed %d" % (rq, r))
    big = 0
    if r + 1 <= n:
        for rs in itertools.combinations(range(n), r + 1):
            for cs in itertools.combinations(range(n), r + 1):
                if det([[M[i][j] for j in cs] for i in rs]) != 0:
                    big += 1
    if big != 0:
        ok = False
        why.append("%d nonzero (r+1)-minors" % big)
    small = any(det([[M[i][j] for j in cs] for i in rs]) != 0
                for rs in itertools.combinations(range(n), r) for cs in itertools.combinations(range(n), r))
    if not small:
        ok = False
        why.append("no nonzero r-minor")
    say("3. rank over Q: elimination %d; nonzero %d x %d minors: %d; a nonzero %d x %d minor exists: %s"
        % (rq, r + 1, r + 1, big, r, r, small))
    if r != R_PINNED:
        ok = False
        why.append("the claimed rank %d is not the statement's 5" % r)
    # 4. the GF(2) factorization of the Lean development
    As, Bs = d["A_gf2"], d["B_gf2"]
    if As != A_LEAN or Bs != B_LEAN:
        ok = False
        why.append("A or B differs from the Lean factors T7A, T7B")
    A = [[int(c) for c in row] for row in As]
    B = [[int(c) for c in row] for row in Bs]
    if len(A) != n or any(len(row) != R_PINNED for row in A) or len(B) != R_PINNED or any(len(row) != n for row in B) \
            or any(x not in (0, 1) for row in A + B for x in row):
        return False, why + ["A is not 7 x 5 or B is not 5 x 7 over {0, 1}"]
    AB = [[sum(A[i][k] * B[k][j] for k in range(R_PINNED)) % 2 for j in range(n)] for i in range(n)]
    diag = all(AB[v][v] == 1 for v in range(n))
    zeros = all(AB[i][j] == 0 for i in range(n) for j in range(n) if arc(W[i], W[j]))
    same = all(AB[i][j] == M[i][j] % 2 for i in range(n) for j in range(n))
    if not (diag and zeros and same):
        ok = False
        why.append("A B mod 2: diagonal 1 %s, zero on the arcs %s, equal to M mod 2 %s" % (diag, zeros, same))
    say("4. Lean factors over GF(2): A B mod 2 has diagonal 1: %s; zeros on all 21 arcs: %s; equals M mod 2: %s"
        % (diag, zeros, same))
    # 5. the lemma on the 18-point transitive clique
    S = [tuple(q) for q in d.get("demo_S", [])]
    idx = {w: i for i, w in enumerate(W)}
    good = len(S) == 18 and len(set(S)) == 18 and all(q[0] in idx and q[1] in idx for q in S)
    if good:
        for i in range(len(S)):
            for j in range(len(S)):
                a0, a1 = idx[S[i][0]], idx[S[i][1]]
                b0, b1 = idx[S[j][0]], idx[S[j][1]]
                kq = M[a0][b0] * M[a1][b1]
                k2 = AB[a0][b0] * AB[a1][b1] % 2
                ordom = arc(S[i][0], S[j][0]) or arc(S[i][1], S[j][1])
                if i == j and (abs(kq) != 1 or k2 != 1):
                    good = False
                if i < j and not ordom:
                    good = False
                if ordom and (kq != 0 or k2 != 0):
                    good = False
    if not good or len(S) > r * r:
        ok = False
        why.append("the lemma demonstration fails on demo_S")
    else:
        say("5. the 18-point transitive clique of the OR-square gives a triangular block of M (x) M with "
            "diagonal +-1 (and 1 through A B mod 2); 18 <= %d" % (r * r))
    return ok, why


def safe(d, say):
    try:
        return check(d, say)
    except (KeyError, ValueError, TypeError, IndexError) as e:
        return False, ["malformed certificate: %r" % (e,)]


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "rank_certificate.json")) as fh:
        d = json.load(fh)
    ok, why = safe(d, print)
    if ok:
        print("PASS: a rank-5 matrix with nonzero diagonal and zeros on the arcs (over Q, and over GF(2) "
              "through the Lean factors): w(T7^n) <= tr(T7^n) <= 5^n for every n, so C(T7) <= 5")
    else:
        print("FAIL: " + "; ".join(why[:4]))
    verdict = ok

    def forged(edit):
        f = json.loads(json.dumps(d))
        edit(f)
        return f

    def on_arc(f):
        f["M"][0][1] = 1

    def diag2(f):
        f["M"][6][6] = 2

    def rank4(f):
        f["rank"] = 4

    def flip_a(f):
        f["A_gf2"][4] = "01111"

    def other_w(f):
        f["W"] = [0, 1, 2, 3, 9, 14, 19]

    for name, edit in (("an entry on the arc 0 -> 1", on_arc), ("the last diagonal entry set to 2", diag2),
                       ("the rank claimed to be 4", rank4), ("one bit of A flipped", flip_a),
                       ("vertex 18 replaced by 19", other_w)):
        fok, fwhy = safe(forged(edit), lambda s: None)
        print("control (%s): %s -- %s" % (name, "FAIL as expected" if not fok else "PASSED, which is wrong",
                                          "; ".join(fwhy[:2])))
        if fok:
            verdict = False
    print("VERDICT: PASS" if verdict else "VERDICT: FAIL")
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
