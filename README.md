# A 7-vertex tournament whose Sperner capacity exceeds the order of its largest transitive subtournament

For a digraph `R` on a finite vertex set, `w(Rⁿ)` is the largest number of words of length `n` over
the vertices such that every ordered pair of distinct words has a coordinate carrying an arc from
the first to the second, and the capacity is `C(R) = lim w(Rⁿ)^{1/n} = sup_n w(Rⁿ)^{1/n}`
(Alon, *On the capacity of digraphs*, European Journal of Combinatorics 19 (1998) 1–5; the Sperner
capacity of Gargano, Körner and Vaccaro is its logarithm). For a tournament `T`, `t(T)` is the number
of vertices of its largest transitive subtournament, and `t(T) ≤ C(T)` always. Conjecture 1.1 of
Alon's paper, attributed there to Körner and Simonyi, reads `C(T) = t(T)` for every tournament; the
same paper disproves it, by a random construction and by the Paley tournament on 67 vertices, and
asks for the smallest tournament for which the equality fails. The answer is seven.

Let `T₇` be the subtournament of the Paley tournament on 23 vertices (`x → y` iff `y − x` is a
nonzero square modulo 23) induced on the residues 0, 1, 2, 3, 9, 14, 18. [Challenge.lean](Challenge.lean)
states nineteen theorems over nine definitions and [Solution.lean](Solution.lean) proves them,
kernel-only; the table in [VERIFICATION.md](VERIFICATION.md) names each one:

- `T₇` is a tournament with `t(T₇) = 4`; eighteen listed points of `T₇ × T₇` form a transitive
  clique of its second Sperner power (every earlier point sends an arc to every later one in some
  coordinate), so by the lift lemma some Sperner power of `T₇` has a clique larger than `4ⁿ`,
  `√18 ≤ C(T₇)`, and `t(T₇) < C(T₇)`: the equality fails on seven vertices;
- `C(T₇) ≤ 5`, by an explicit rank-5 factorization over `GF(2)` of a matrix with nonzero diagonal
  and zeros on the arcs (the rank bound);
- every tournament on at most six vertices satisfies `C(T) = t(T)`: for each of the 1, 1, 1, 2, 4,
  12, 56 isomorphism classes on 0 to 6 vertices a representative with a rank-`t` factorization over
  `GF(2)` and a transitive `t`-chain, and a kernel check that every labelled tournament on at most
  six vertices is a relabelling of a representative; hence a tournament with `t(T) < C(T)` has at
  least seven vertices, and seven is exactly the least order of a counterexample;
- the general tools: the lift lemma, `N^{1/k} ≤ C(R)` for `N` such points of the `k`-th power,
  `t(R) ≤ C(R)`, the rank bound `C(R) ≤ r` for any factorization through `Fʳ`, and `C(R) ≤ |V|`;
- the Paley tournament on 23 vertices has `t = 5` and `√29 ≤ C`, from a 29-point transitive clique
  of its second Sperner power.

On paper, in [note/](note/README.md), with standard-library certificates: the square value 18 is
exact; on seven vertices, 455 of the 456 isomorphism classes have a rank-`t` matrix over `GF(2)` and
the exception is `T₇`, which is therefore the unique smallest counterexample up to isomorphism; every
proper subtournament of `T₇` satisfies the equality; `√18 ≤ C(T₇) ≤ 5`; the Paley tournament on 7
vertices has `C = 3`. The smallest example previously exhibited has 67 vertices; examples on 27 and
26 vertices follow from Alon's argument over `GF(27)` with a published value of `t`, and are
re-verified in the note.

Not claimed: the exact value of `C(T₇)`; in Lean, anything about tournaments on seven or more
vertices other than `T₇` and the Paley tournament on 23 vertices (the uniqueness of `T₇` and the
exact square value are certificates, not Lean theorems).

> As of 2026-10-08 (UTC), no tournament on fewer than 67 vertices whose capacity exceeds its
> transitive number, no determination of the capacity of every tournament on six vertices, and no
> statement that the smallest counterexample has seven vertices or is unique, was located in Alon's
> paper and his survey *Graph powers*, Körner's 1998 paper, Kiviluoto–Östergård–Vaskelainen's
> *Sperner capacity of small digraphs* (which settles every digraph on at most five vertices except
> eight that are not tournaments), Vaskelainen's thesis, Simonyi's 2006 dissertation, the arXiv
> literature on Sperner capacity, zbMATH, Google Scholar, the Palomar registry, Hexagon, openai/math
> or the formal-conjectures repository. The lift lemma and the rank bound are standard in substance
> (Sali–Simonyi 1999; Kiviluoto–Östergård–Vaskelainen 2009, Theorem 4); what is new is their values
> on `T₇` and the classification of the small tournaments.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are
pinned by the committed manifest; there are no GitHub Actions workflows.

```sh
python scripts/verify.py --fetch-cache
```

runs every check (the pins, the source guard, the definition and statement comparisons, the
certificates, the build with the axiom audit, the module-resolution check, the elaboration check of
the nine definitions against the Challenge, and Palomar's core-notation audit);
[VERIFICATION.md](VERIFICATION.md) lists them and their limits. [PROOF.md](PROOF.md) gives the
mathematics with the Lean name of every step, [DISCLOSURE.md](DISCLOSURE.md) the assistance
statement, and [note/](note/README.md) the research note (CC BY-SA 4.0) with its certificates.

License: [MIT](LICENSE).
