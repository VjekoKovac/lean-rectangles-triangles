# Rectangles, triangles and Schrödinger waves

Lean 4 proofs of all four theorems in the introduction of *Rectangles, triangles and Schrödinger waves*, by Jonathan Bennett, Vjekoslav Kovač, Shohei Nakamura, and Itamar Oliveira. The formalization authors are the same four authors. The original mathematical source is the first arXiv version, dated 29 June 2026. Item 1.1 is a question. [Paper on arXiv](https://arxiv.org/abs/2606.30178v1) · [Versioned PDF](https://arxiv.org/pdf/2606.30178v1)

## The four theorems

For the statements in conventional notation, including all the domains, normalizations and quantifiers, read [the statement guide](STATEMENTS.md). For the commands, their output and the scope of each check, read [the verification record](evidence/README.md).

Here $N$ is a **real** frequency or box radius and $n$ is an **exact** support cardinality. In the table, MT means Mizohata–Takeuchi. Each proof guide specifies the definitions, hypotheses, proof steps, and corresponding Lean declarations.

| Paper | Public Lean declaration | Assertion | Proof guide |
| --- | --- | --- | --- |
| 1.2, p. 3 | `RTS.combinatorial_growth` | For one absolute $c>0$, the unpinned extremum dominates the pinned extremum, which is at least $(\log x)^{c/\log\log\log x}$ both for every sufficiently large radius $x=N$ and for every sufficiently large cardinality $x=n$. | [Finite fields, lattice lifting, and interpolation](blueprints/01-combinatorics.md) |
| 1.3, p. 8 | `RTS.quantitative_transference` | For every $d\ge1$ and $N\ge1$, each periodic constant at $N$, Stein or MT, is at most its Euclidean counterpart at $N+1$, with coefficient one. | [Transference and packet limits](blueprints/02-transference.md) |
| 1.4, p. 8 | `RTS.configuration_lower_bounds` | In dimension two, for every $N\ge1$ and $n\ge1$, the box and cardinality Stein constants dominate the respective unpinned configuration ratios. Both MT constants dominate the corresponding pinned ratios. All four comparisons have coefficient one. | [The fourth moment and ray counts](blueprints/03-configuration.md) |
| 1.5, p. 9 | `RTS.trigonometric_growth` | In every dimension $d\ge1$, both periodic constants are at least $c_d(\log N)^d$ for all sufficiently large $N$. At every sufficiently large $n$, each cardinality constant lies between $c'_d n$ and $C_d n$. The three multiplicative constants are positive and finite. | [Dyadic frequencies and exact support sizes](blueprints/04-weights.md) |

[Challenge.lean](Challenge.lean) contains the mathematical definitions and the four reference statements, with only mathlib imports. Its four `by sorry` placeholders mark the propositions posed to the independent solution. [Solution.lean](Solution.lean) gives four proved declarations with the same names in a separate import tree. The [axiom report](evidence/axioms.txt) lists exactly `propext`, `Classical.choice`, and `Quot.sound` for each solution theorem. The [Comparator configuration](comparator.json) selects all four together. **Both NanoDa and the Lean kernel accepted the solution.** Comparator exited with status 0. The [comparison transcript](evidence/comparator.txt) records the complete command and output.

## Sources, proof choices, and review

- Theorem 1.2 reuses `chebyshev_asymptotic_pnt` from the PrimeNumberTheoremAnd project to select primes congruent to three modulo four. Mathlib supplies the Chinese remainder equivalence `ZMod.prodEquivPi` and the quadratic nonresidue lemma `ZMod.mod_four_ne_three_of_sq_eq_neg_one`. The lift retains enough primitive directions to prove the lower rectangle count and upper pinned-triangle count used in the conclusion. The first guide distinguishes these estimates from the paper’s more precise auxiliary asymptotic formulas. [PrimeNumberTheoremAnd source](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/a4fb6989b07e9c76b511807ae93e33e25b820e9b) · [Mathlib source](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
- Theorem 1.3 uses translated rectangular packets in frequency space and mathlib’s torus Parseval theorem, `UnitAddTorus.hasSum_sq_mFourierCoeff`, formalized by David Loeffler. The guide explains how the common packet mass cancels, retaining the sharp transfer coefficient. Theorem 1.5 uses the same dyadic construction as the paper and directly injects marked choices into the resulting collision count. [Packet identity](RTS/PacketIdentities.lean) · [Dyadic multiplicity proof](RTS/WeightMultiplicity.lean)
- Codex generated the proof files. Separate AI reviews compared the source to the challenge and inspected the proof and its readability. The statement review discusses the choice of a lower integral on exceptional line restrictions of measurable weights. A human coauthor’s sign-off and Palomar’s editorial review are separate from the recorded machine checks. [Statement fidelity](reviews/statement-fidelity.md) · [Proof correctness and clarity](reviews/proof-correctness.md)





