# The four theorems in mathematical notation

The source is Jonathan Bennett, Vjekoslav Kovač, Shohei Nakamura and Itamar Oliveira, *Rectangles, triangles and Schrödinger waves*. Theorem 1.2 is on printed page 3, Theorems 1.3 and 1.4 on page 8, and Theorem 1.5 on page 9. Item 1.1 is a question. [arXiv:2606.30178v1](https://arxiv.org/abs/2606.30178v1)

| Theorem | Proposition defined in the Challenge | Proved declaration in the Solution | Proof guide |
| --- | --- | --- | --- |
| 1.2 | `RTS.CombinatorialGrowth` | `RTS.combinatorial_growth` | [Finite fields, lifting and growth](blueprints/01-combinatorics.md) |
| 1.3 | `RTS.QuantitativeTransference` | `RTS.quantitative_transference` | [Transference](blueprints/02-transference.md) |
| 1.4 | `RTS.ConfigurationLowerBounds` | `RTS.configuration_lower_bounds` | [Configuration tests](blueprints/03-configuration.md) |
| 1.5 | `RTS.TrigonometricGrowth` | `RTS.trigonometric_growth` | [Trigonometric weights](blueprints/04-weights.md) |

In Lean, a name beginning with a capital letter in this table denotes a proposition. For example, `RTS.CombinatorialGrowth` expands into a statement about lattice counts. The lowercase theorem supplies its proof. The standalone definitions and the four proof entries are in [Challenge.lean](Challenge.lean) and [Solution.lean](Solution.lean).

## The lattice counts

Let $A$ be a nonempty finite subset of $\mathbb Z^2$. Write $B(A)$ for the number of ordered quadruples $(a,b,c,e)\in A^4$ satisfying

$$
a+c=b+e,\qquad (b-a)\cdot(e-a)=0.
$$

For each $k\in A$, let $T_k(A)$ be the number of ordered pairs $(a,b)\in A^2$ satisfying

$$
(2k-a-b)\cdot(b-a)=0.
$$

This equation says that the two vertices are equidistant from the apex $k$. Both counts include repeated points. In particular, the pairs $(a,a)$ give $T_k(A)\geq |A|$. Define

$$
r(A)=\frac{B(A)}{\sum_{k\in A}T_k(A)},\qquad
r_{\mathrm{pin}}(A)=\frac{B(A)}{|A|\max_{k\in A}T_k(A)}.
$$

For a real radius $N\geq1$, write $\mathfrak R(N)$ and $\mathfrak R^{\mathrm{pin}}(N)$ for the maxima of these respective ratios over all nonempty $A\subseteq[-N,N]^2\cap\mathbb Z^2$. Lean takes the supremum of this finite nonempty family. For an integer $n\geq1$, write $\widetilde{\mathfrak R}(n)$ and $\widetilde{\mathfrak R}^{\mathrm{pin}}(n)$ for the corresponding suprema over all $A\subseteq\mathbb Z^2$ with $|A|=n$, with unrestricted locations. The four Lean names are `boxRatio`, `pinnedBoxRatio`, `sizeRatio` and `pinnedSizeRatio` in namespace `RTS`.

### Theorem 1.2

Put $G_c(x)=(\log x)^{c/\log(\log(\log x))}$, with natural logarithms. There exist a **single** real $c>0$, a real threshold $N_0$, and a positive integer $n_0$ such that

$$
\begin{aligned}
\mathfrak R(N)&\geq\mathfrak R^{\mathrm{pin}}(N)\geq G_c(N)
&&\text{for every real }N\geq N_0,\\
\widetilde{\mathfrak R}(n)&\geq\widetilde{\mathfrak R}^{\mathrm{pin}}(n)\geq G_c(n)
&&\text{for every integer }n\geq n_0.
\end{aligned}
$$

The Lean proposition permits any real witness $N_0$. Increasing the witness preserves the conclusion, so the estimate applies where all three ordinary logarithms in the denominator are defined and the denominator is positive.

## The weighted Schrödinger constants

Use $\mathbb T=\mathbb R/\mathbb Z$, $e(s)=\exp(2\pi i s)$, and normalized Haar measure on every torus. In dimension $d\geq1$, periodic data are finitely supported complex coefficients $a_k$, $k\in\mathbb Z^d$, with support $A=\{k:a_k\ne0\}$. Euclidean data are given in Fourier variables by $F=\widehat u_0\in L^2(\mathbb R^d)$. Let $K$ be its essential closed support, defined in Lean as the support of the measure $|F(\xi)|^2\,d\xi$. All Euclidean data used in the radius-$N$ estimates have $K\subseteq[-N,N]^d$. With these conventions the waves are

$$
u_{\mathbb T}(x,t)=\sum_{k\in A}a_k e(x\cdot k+t|k|^2),
\qquad
u_{\mathbb R}(x,t)=\int_{\mathbb R^d}F(\xi)e(x\cdot\xi+t|\xi|^2)\,d\xi .
$$

On the torus, $w$ is a pointwise nonnegative integrable real function on $\mathbb T^d\times\mathbb T$. In Euclidean space, $w$ is a pointwise nonnegative locally integrable real function on $\mathbb R^d\times\mathbb R$. For the respective spatial suprema of their ray integrals define

$$
X_{\mathbb T}(k)=\sup_{x\in\mathbb T^d}\int_{\mathbb T}w(x-2tk,t)\,dt,
\qquad
X_{\mathbb R}(v)=\sup_{x\in\mathbb R^d}\int_{\mathbb R}w(x-2tv,t)\,dt.
$$

Here $x-2tk$ is taken modulo $\mathbb Z^d$. The suprema are pointwise. For nonnegative integrands Lean uses the extended lower Lebesgue integral. On a measurable line restriction this is the ordinary nonnegative integral. This specifies the convention on exceptional lines for completed-measure representatives. The source-to-Lean review discusses its scope. [Statement-fidelity review](reviews/statement-fidelity.md)

The common left sides in the two settings are

$$
L_{\mathbb T}=\int_{\mathbb T}\int_{\mathbb T^d}|u_{\mathbb T}(x,t)|^2 w(x,t)\,dx\,dt,
\qquad
L_{\mathbb R}=\int_0^1\int_{\mathbb R^d}|u_{\mathbb R}(x,t)|^2 w(x,t)\,dx\,dt.
$$

The right sides depend on the type of estimate.

$$
\begin{aligned}
D^{S}_{\mathbb T}&=\sum_{k\in A}|a_k|^2 X_{\mathbb T}(k),
& D^{M}_{\mathbb T}&=\left(\sum_{k\in A}|a_k|^2\right)\sup_{k\in A} X_{\mathbb T}(k),\\
D^{S}_{\mathbb R}&=\int_{\mathbb R^d}|F(v)|^2 X_{\mathbb R}(v)\,dv,
& D^{M}_{\mathbb R}&=\left(\int_{\mathbb R^d}|F(v)|^2\,dv\right)\sup_{v\in K} X_{\mathbb R}(v).
\end{aligned}
$$

For each $S$ (Stein) or $M$ (Mizohata–Takeuchi) estimate, the best constant is the infimum of $C\in[0,\infty]$ such that $L\leq C D$ for **every** eligible datum and **every** eligible weight. In particular, the energy in the MT denominator is the Fourier-side expression for $\|u_0\|_2^2$. The numerator in Euclidean space uses $0\leq t\leq1$, whereas the Euclidean ray integral uses all $t\in\mathbb R$.

| Family | Allowed support | Lean names in `RTS` |
| --- | --- | --- |
| $\mathfrak S_{\mathbb R^d}(N),\mathfrak M_{\mathbb R^d}(N)$ | $K\subseteq[-N,N]^d$ | `eucStein d N`, `eucMT d N` |
| $\mathfrak S_{\mathbb T^d}(N),\mathfrak M_{\mathbb T^d}(N)$ | $A\subseteq[-N,N]^d\cap\mathbb Z^d$ | `perStein d N`, `perMT d N` |
| $\widetilde{\mathfrak S}_{\mathbb T^d}(n),\widetilde{\mathfrak M}_{\mathbb T^d}(n)$ | Exactly $n$ distinct frequencies with nonzero coefficients, anywhere in $\mathbb Z^d$ | `perSteinCard d n`, `perMTCard d n` |

### Theorem 1.3

For every integer $d\geq1$ and every real $N\geq1$,

$$
\mathfrak S_{\mathbb T^d}(N)\leq\mathfrak S_{\mathbb R^d}(N+1),
\qquad
\mathfrak M_{\mathbb T^d}(N)\leq\mathfrak M_{\mathbb R^d}(N+1).
$$

Both comparisons have coefficient one. The enlargement by one is in the coordinate radius on the Euclidean side.

### Theorem 1.4

In dimension two, for every real $N\geq1$ and every integer $n\geq1$,

$$
\begin{aligned}
\mathfrak S_{\mathbb T^2}(N)&\geq\mathfrak R(N),
&\widetilde{\mathfrak S}_{\mathbb T^2}(n)&\geq\widetilde{\mathfrak R}(n),\\
\mathfrak M_{\mathbb T^2}(N)&\geq\mathfrak R^{\mathrm{pin}}(N),
&\widetilde{\mathfrak M}_{\mathbb T^2}(n)&\geq\widetilde{\mathfrak R}^{\mathrm{pin}}(n).
\end{aligned}
$$

The multiplier in each bound is exactly one. For comparison, Lean maps the nonnegative real configuration ratios into its extended nonnegative reals using `ENNReal.ofReal`.

### Theorem 1.5

For every fixed integer $d\geq1$ there exist real $c_d>0$ and $N_d\geq1$ such that, for every real $N\geq N_d$,

$$
\mathfrak S_{\mathbb T^d}(N)\geq c_d(\log N)^d,
\qquad
\mathfrak M_{\mathbb T^d}(N)\geq c_d(\log N)^d.
$$

For the same $d$, there exist finite reals $b_d,B_d>0$ and an integer $n_d\geq1$ such that, for every integer $n\geq n_d$,

$$
b_d n\leq\widetilde{\mathfrak S}_{\mathbb T^d}(n)\leq B_d n,
\qquad
b_d n\leq\widetilde{\mathfrak M}_{\mathbb T^d}(n)\leq B_d n.
$$

The constants and thresholds may depend on $d$. They are uniform in $N$ or $n$ within their respective families. The formal statement expands the paper's $\sim_d n$ into all four cardinality comparisons.
