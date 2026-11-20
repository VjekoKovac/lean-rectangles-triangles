# The lacunary trigonometric weights

**Target.** Theorem 1.5, source label `thm:d1-log-intro`. For each positive integer
dimension $d$, both periodic constants for the real box scale $N$ dominate
$c_d(\log N)^d$ for every sufficiently large $N$. At exact support size $n$,
both lie between $c'_d n$ and $C'_d n$ for every sufficiently large positive
integer $n$. The three positive constants and the two thresholds may depend on
$d$. The source proves the cardinality estimates with explicit bounds $n/4$
and $n$. All four constants have the same definitions as in Theorems 1.3–1.4.

## Source proof in detail

1. Choose integers $m_l\ge 1$, put $r_l=\lfloor m_l/2\rfloor$, and let $M_l$
   be the sum of the earlier lengths. The data have coefficient 1 on the product
   of the sets of frequencies $2^{M_l+j}$ for $1\le j\le m_l$. Thus there
   are $\prod_l m_l$ frequencies in the box of radius $2^{\sum_l m_l}$.
2. For each coordinate take all its $r_l$-element subsets $J_l$. The
   auxiliary polynomial sums the characters with spatial components
   $X_{l,J}=\sum_{j\in J}2^{M_l+j}$ and time frequency
   $\sum_l Y_{l,J_l}$, where $Y_{l,J}=\sum_{j\in J}4^{M_l+j}$.
   The test weight is its squared modulus, so is continuous and nonnegative.
3. Test at every $k_l=2^{M_l+q_l}$ in the support. On the geodesic $x-2tk$,
   integration removes nonconstant time characters. For a pair of subset tuples,
   take $c_{l,j}=1_{J_l}(j)-1_{J'_l}(j)$. The surviving relation is the sum
   of these coefficients times $2^{2M_l}(2^{2j}-2^{j+q_l+1})$. The term
   at $j=q_l+1$, if present, is zero. On every other term the exact power of
   two dividing it has exponent $2M_l+\min(2j,j+q_l+1)$. These exponents
   are strictly increasing within each block, and the ranges for different
   coordinates are disjoint. A nonzero signed sum would therefore have exactly
   one odd term after division by its common power of two. All nonexceptional
   coefficients vanish. Equality of the two subset cardinalities in each
   coordinate forces the exceptional coefficient to vanish too. Only diagonal
   terms survive, so each geodesic integral equals $\prod_l {m_l\choose r_l}$.
4. In the product of the solution with the auxiliary polynomial, adjoin a fresh
   index to each subset. A resulting tuple of $(r_l+1)$-element subsets has
   $\prod_l(r_l+1)$ marked choices. Binary expansion distinguishes its spatial
   frequency from those of all other tuples. All coefficients in this expansion
   are positive, even if other terms contribute to the same frequency.
   Orthogonality bounds the squared norm from below by
   $\prod_l (r_l+1)^2 {m_l\choose r_l+1}$.
5. Divide the preceding lower bound by the common Stein and Mizohata–Takeuchi
   test denominator $\prod_l m_l{m_l\choose r_l}$. The quotient simplifies to
   $\prod_l (r_l+1)(m_l-r_l)/m_l\ge\prod_l m_l/4^d$.
   Equal lengths $m_l=\lfloor\log N/(d\log 2)\rfloor$ give the box estimate
   for every sufficiently large real $N$. Lengths $(n,1,\ldots,1)$ give
   the lower bound $n/4$, since each length-one factor is exactly one.
6. For arbitrary coefficients and weights, Cauchy–Schwarz gives
   $|u|^2\le n\sum_k|a_k|^2$. Haar invariance and Fubini show that each
   tested line maximum dominates the space-time mean of the weight. Multiply
   by $|a_k|^2$, sum, and compare the two right-hand sides to obtain
   $\widetilde{\mathfrak M}\le\widetilde{\mathfrak S}\le n$.

The analytic definitions and the target occur in `RTS/AnalysisDefs.lean` and
`RTS/WeightStatement.lean`. The exact scope of completed lemmas is recorded in
the repository verification report.

## Lean proof map

| Mathematical step | Checked declaration |
|---|---|
| Dyadic factorization and the unique odd summand | `RTS.Dyadic.timeTerm_factor`, `sum_ne_zero_of_distinct_orders` |
| Coordinate separation and signed-coefficient rigidity | `RTS.Dyadic.orders_injective`, `signed_dyadic_rigidity` |
| Equality of line frequencies implies equality of the subset tuples | `RTS.Dyadic.lineFreq_injOn` |
| Support cardinality, box inclusion, and validity of the weight | `RTS.Dyadic.data_card`, `data_in_box`, `weight_valid` |
| Exact X-ray and denominator bound | `RTS.Dyadic.dyadicXray`, `dyadicMTDenom_le` |
| Expansion and exact energy | `RTS.Dyadic.wave_mul_auxPoly`, `dyadicLHScollisions` |
| Marked subset tuples inject into collisions | `RTS.Dyadic.collision_count_lower` |
| Adjacent binomial ratio and explicit lower bound | `RTS.Dyadic.dyadic_binomial_ratio`, `quarter_le_dyadic_ratio`, `test_quotient` |
| Pointwise Cauchy–Schwarz, Haar averaging, and cardinality upper bound | `RTS.perWave_sq_le`, `perXray_average`, `perSteinCard_le_card` |
| Real radii and exact support sizes | `RTS.Dyadic.exists_log_scale`, `trigonometricGrowth_of_dyadic` |
| Unconditional theorem | `RTS.Dyadic.trigonometricGrowth` |

The source lower-bounds the energy by collecting coefficients of distinct
binary subset sums. The Lean proof counts the same marked pairs directly in
the collision sum from Parseval. Each pair retains both marks and their common
enlarged subset, so it has an explicit inverse on its image. This avoids a
separate unique-binary-expansion lemma and gives the same product of binomial
coefficients. The noncollision argument on a geodesic, including the index
$q_l+1$, follows the source.

The proof uses mathlib's finite-character orthogonality, finite sums and
products, and `Nat.choose_succ_right_eq` from `Mathlib.Data.Nat.Choose.Basic`
for the binomial recurrence. The arithmetic proofs use the kernel-checked
`omega`, `ring`, `norm_num`, and `linarith` tactic families. The stored build
and axiom reports give the versions and replay commands for these declarations.
