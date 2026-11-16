# Inequalities from Kozma's "Useful Inequalities"

Formal proofs of inequalities from László Kozma's sheet "Useful Inequalities"
(version 0.44).

## Files

| File | Contents |
|---|---|
| `finite_sums.ml` | Inequalities about finite sums and products of reals |
| `combinatorics.ml` | Inequalities about finite set systems and prefix-free codes |
| `real_lemmas.ml` | General results of real analysis used by the files below |
| `bernoulli_exp.ml` | Bernoulli's inequality and bounds on the exponential |
| `log_trig_sqrt.ml` | Bounds on the logarithm, trigonometric and hyperbolic functions and square roots |
| `means.ml` | Inequalities between means and weighted products |
| `binomial_entropy.ml` | Binomial coefficients, Stirling's formula and the binary entropy |
| `convexity.ml` | Convexity, majorization and integral inequalities |
| `series.ml` | Series inequalities (Mathieu, Hilbert, Hardy) |
| `probability_basic.ml` | Planned: moment and tail inequalities for one random variable |
| `probability_concentration.ml` | Planned: concentration inequalities for sums of random variables |
| `probability_maximal.ml` | Planned: maximal inequalities, martingales, Janson and Lovász |
| `matrix.ml` | Planned: matrix inequalities |

To load all files:

```
needs "kozma/make.ml";;
```

## The sheet's inequalities

One row per entry of the sheet, grouped by file. Theorems: the theorems that state the
entry, or "planned" (not yet formalized) or "deferred" (left for later, as research
scope). Remarks: how the statement differs from the printed one, or "As printed."

### Finite sums (`finite_sums.ml`)

| Entry | Theorems | Remarks |
|---|---|---|
| Cauchy-Schwarz | `CAUCHY_SCHWARZ_INEQUALITY` | Any finite index set. |
| Chebyshev (sum form) | `CHEBYSHEV_SUM_INEQUALITY` | Any finite index set. Does not assume x_1 <= ... <= x_n, and f, g need be nondecreasing only on the values x_i. |
| Rearrangement 1 | `REARRANGEMENT_INEQUALITY` | As printed. |
| Rearrangement 2 | `REARRANGEMENT_INEQUALITY_GEN` | b nondecreasing, the condition printed on the first rearrangement line. |
| Rearrangement 3 | `REARRANGEMENT_INEQUALITY_PRODUCT` | Needs only a_i + b_j >= 0 for all i, j instead of a_i, b_i >= 0; a and b nondecreasing, as on the first line. |
| Kantorovich | `KANTOROVICH_INEQUALITY` | Any finite index set. Does not assume x_i, y_i > 0; 0 < m <= x_i / y_i <= M suffices. |
| Nesbitt | `NESBITT_INEQUALITY`, `NESBITT_INEQUALITY_ALT` | Any finite index set, and every n. The terms a_i / (S - a_i) are undefined when a_i = S, so a_i < S is assumed; a_i >= 0 is not needed. |
| Chong | `SUM_RATIO_PERMUTE_GE`; `PRODUCT_RPOW_PERMUTE_LE` (in `means.ml`) | The first part over any finite index set. The second part is in `means.ml`, over any finite index set and for a_i >= 0 (with 0^0 = 1). |
| Shapiro | `CYCLIC_RATIO_SUM_3_GE`, `CYCLIC_RATIO_SUM_4_GE` | Only the cases n = 3, 4 are proved; for n = 3 only the sums x_{i+1} + x_{i+2} need be positive. |
| Aczél | `ACZEL_INEQUALITY`, `ACZEL_INEQUALITY_ALT`, `ACZEL_INEQUALITY_GEN` | Split by the two alternative hypotheses, which are relaxed to non-strict ones; both are instances of a general form with any reals u, v in place of a_1, b_1 over any finite index set. |
| Abel | `ABEL_INEQUALITY`, `SUM_MUL_DECREASING_BOUNDS` | The minimum and maximum of the partial sums are written as inf and sup of the (finite) set of partial sums, for n >= 1. |
| Milne | `MILNE_INEQUALITY` | Any finite index set. A term with a_i + b_i = 0 has value 0. |
| Sum & product 1 | `PRODUCT_ABS_SUB_LE` | Any finite index set. |
| Sum & product 2 | `PRODUCT_ADD_POW_LE` | Any finite index set. Holds for t >= 0, and a_i >= 0 suffices. |
| Samuelson | `SAMUELSON_INEQUALITY` | Any nonempty finite index set. The two bounds are combined into one bound on \|x_i - mu\|. |

### Set systems and codes (`combinatorics.ml`)

| Entry | Theorems | Remarks |
|---|---|---|
| Kraft | `KRAFT_INEQUALITY`, `KRAFT_INEQUALITY_GEN` | The leaves of a binary tree are modelled as a prefix-free set of words (a leaf's depth is the length of its word). The inequality is proved for every prefix-free set of words over any finite alphabet; for an infinite prefix-free set it applies to every finite subset. |
| LYM | `LYM_INEQUALITY` | Antichains of subsets of any finite set instead of {1, ..., n}. |
| FKG | `FKG_INEQUALITY`, `FKG_INEQUALITY_ALT` | "Monotone" is read as both increasing or both decreasing; the two cases are separate theorems, over any finite ground set. |
| Shearer | `SHEARER_INEQUALITY_COUNTEREXAMPLE`, `SHEARER_INEQUALITY`, `SHEARER_INEQUALITY_GEN` | False as printed when A is empty, t = 0 and the family is nonempty (1 <= 0). This case is excluded and the printed form is refuted. Proved over any finite ground set, for any finite family, including families with repeated sets; the members need not be subsets of the ground set. |
| Sauer-Shelah | `SAUER_SHELAH_INEQUALITY`, `CARD_LE_SHATTERED`, `CARD_SHATTERED_LE_NSUM_BINOM`, `NSUM_BINOM_LE_POW`, `VC_DIMENSION` | str(A) is the set of shattered sets and vc(A) its largest size. The chain holds for every set system over a finite ground set, including the empty set system, for which vc is not defined. |

### Bernoulli and exponential (`bernoulli_exp.ml`)

| Entry | Theorems | Remarks |
|---|---|---|
| Bernoulli 1 | `RPOW_BERNOULLI`, `RPOW_BERNOULLI_REV` | (1 + x)^r is undefined at x = -1 for r < 0, which is excluded. |
| Bernoulli 2 | `RPOW_BERNOULLI_INV` | x < 1/r is written r x < 1; holds for r >= 0 and for r <= -1. |
| Bernoulli 3 | `RPOW_BERNOULLI_NEG` | Holds for all x > -1. |
| Bernoulli 4 | `RPOW_BERNOULLI_CHORD` | As printed. |
| Bernoulli 5 | `BERNOULLI_POW_SUC` | Holds whenever (n + 1) x >= -1, and for every x when n is odd. |
| Bernoulli 6 | `BINOMIAL_POW_LE` | Includes n = 0, and needs only a >= 0 and a + b >= 0 (b may be negative). |
| Exponential 1 | `REAL_EXP_RPOW_LIMIT_BOUNDS` | Holds for x >= -n (real n >= 1). |
| Exponential 2 | `REAL_EXP_POW_FACT_LE`, `REAL_EXP_RPOW_DIV_BOUNDS` | Holds for x >= 0, with n a natural number >= 1 in the n! bound and real n > 0 elsewhere. |
| Exponential 3 | `RPOW_ADD_RPOW_GT_1`, `RPOW_GT_DIV_ADD`, `RPOW_GT_DIV_ADD_COUNTEREXAMPLE`, `REAL_EXP_RPOW_BOUNDS` | x^y > x / (x + y) is false for x = 1/2, y = 4. The printed form is refuted and the inequality is proved for y <= 1 or x >= 1. |
| Exponential 4 | `RPOW_SELF_BOUNDS`, `REAL_EXP_DOUBLE_LE` | e^(2x) <= (1 + x)/(1 - x) holds on [0, 1). |
| Exponential 5 | `RPOW_ROOT_SUB_LE`, `RPOW_TWO_NEG_LE` | The first bound holds for x >= 0 with r >= 1, and for x > 0 with r < 0. |
| Exponential 6 | `REAL_EXP_SQUARE_BOUNDS` | As printed. |
| Exponential 7 | `REAL_EXP_NEG_LE_LINEAR`, `REAL_EXP_NEG_LE_LINEAR_GEN`, `REAL_EXP_QUADRATIC_UPPER`, `REAL_EXP_QUADRATIC_UPPER_GEN` | The bounds hold up to any threshold where they hold at the threshold; e^x <= 1 + x + x^2 is stated for x <= 1.79. |
| Exponential 8 | `RPOW_ADD_DIV_MONO`, `RPOW_ADD_DIV_MONO_NEG`, `RPOW_ADD_DIV_POS_LE_NEG` | The five sign cases are covered, with their boundary cases, by three theorems. |

### Logarithm, trigonometric and hyperbolic functions, square roots (`log_trig_sqrt.ml`)

| Entry | Theorems | Remarks |
|---|---|---|
| Logarithm 1 | `LOG_RATIONAL_BOUNDS` | As printed. |
| Logarithm 2 | `LOG_SQRT_BOUNDS` | ln(1 + x)/x is undefined at x = 0, so the two links that contain it assume x <> 0. |
| Logarithm 3 | `LOG_HARMONIC_BOUNDS`, `LOG_SUC_BOUNDS` | The first two links hold for every real n > 0. |
| Logarithm 4 | `LOG_BOUNDS_MISC`, `LOG_ABS_LE_HALF_DIFF_INV`, `LOG_ADD_LE_DIV`, `LOG_LE_RPOW_ROOT` | \|ln x\| <= \|x - 1/x\|/2 needs only x > 0, and ln(x + y) <= ln x + y/x only x > 0 and x + y > 0. |
| Logarithm 5 | `LOG_QUADRATIC_LOWER` | As printed. |
| Trigonometric | `TRIGONOMETRIC_BOUNDS` | Assumes x in [0, pi/2], the condition printed at the end of the second hyperbolic line. The cube root is written root 3. |
| Hyperbolic 1 | `HYPERBOLIC_SINH_BOUNDS`, `MUL_COS_HALF_SQUARE_LE_SIN`, `SIN_LE_CUSA` | Assumes x in [0, pi/2], the condition printed at the end of the second hyperbolic line. sinh x is written (e^x - 1/e^x)/2, the form HOL Light's library uses. At x = 0 the terms x^3/sinh^2 x and x^2/sinh x are 0. x cos^2(x/2) <= sin x holds on [0, pi], and sin x <= (x cos x + 2x)/3 for all x >= 0. |
| Hyperbolic 2 | `SIN_DIV_BOUNDS`, `SIN_MUL_BOUNDS` | sin x / x is undefined at 0 and tan x at pi/2, so the line assumes x > 0 and its last link x < pi/2; it is also proved multiplied by x on the closed interval. sin x <= x cos(x/2) holds on [0, pi]. |
| Square root 1 | `SQRT_DIFFERENCE_BOUNDS` | The first link holds for every x > 0. |
| Square root 2 | `SQRT_QUADRATIC_BOUNDS` | The middle link holds for every x >= 0. |

### Means (`means.ml`)

| Entry | Theorems | Remarks |
|---|---|---|
| Minkowski | `MINKOWSKI_INEQUALITY` | Any finite index set. |
| Hölder | `HOELDER_SUM_INEQUALITY` | Any finite index set; p, q > 0, 1/p + 1/q = 1. |
| Means 1 | `MEANS_INEQUALITY`, `MEANS_INEQUALITY_POS_LE`, `MEAN_LE_QUADRATIC_MEAN`, `QUADRATIC_MEAN_LE_CONTRAHARMONIC_MEAN` | Any nonempty finite index set; min and max are inf and sup of the finite set of values. The chain holds for x_i > 0, its links from GM on for x_i >= 0, AM <= QM for all real x_i, and QM <= sum x_i^2 / sum x_i for real x_i with sum x_i > 0. |
| Means 2 | `SUM_ABS_RATIO_BOUNDS`, `SUM_DIV_SUM_BOUNDS` | Any nonempty finite index set; min and max are inf and sup of the finite set of values. Needs y_i <> 0; also proved as the mediant inequality for real a_i and b_i > 0. |
| Power means | `POWER_MEAN_MONO`, `POWER_MEAN_BOUNDS`, `POWER_MEAN_LIMIT_POSINF`, `POWER_MEAN_LIMIT_NEGINF`, `POWER_MEAN_LIMIT_ZERO`, `POWER_MEAN_LIMIT_ZERO_RIGHT`, `POWER_MEAN_LIMIT_COUNTEREXAMPLE` | Any finite index set. M_p is `power_mean`, with M_0 = prod \|x_i\|^w_i; for p < 0, x_i <> 0 wherever w_i > 0. The printed limits min x_i and max x_i are false (x = (-2, 1), w = (1/2, 1/2)); the limits are min and max of \|x_i\| over w_i > 0, and the limit at 0 holds from the right for every x. |
| Lehmer | `LEHMER_INEQUALITY` | Any finite index set. For p < 1, x_i <> 0 wherever w_i > 0; no hypothesis on the denominators. |
| Log mean | `LOG_MEAN_INEQUALITY`, `LOG_MEAN_OUTER_BOUNDS` | Assumes x <> y; the outer links hold for x, y >= 0. |
| Heinz | `HEINZ_INEQUALITY` | Holds for x, y >= 0. |
| Maclaurin-Newton | `NEWTON_INEQUALITY`, `MACLAURIN_INEQUALITY` | Any finite index set. S_k is `symmetric_mean` (the mean over k-subsets). Newton holds for all real a_i and every k >= 1; Maclaurin for every k >= 1 and a_i >= 0. |
| Weierstrass 1 | `PRODUCT_RPOW_ONE_SUB_GE` | Any finite index set. |
| Weierstrass 2 | `PRODUCT_RPOW_ONE_ADD_GE`, `PRODUCT_RPOW_ONE_ADD_LE_ONE_SUB` | Any finite index set. The right link holds for x_i in [-1,1) and w_i >= 0; the left link holds for all x_i >= 0. |
| Weierstrass 3 | `PRODUCT_RPOW_ONE_ADD_LE_INV`, `PRODUCT_RPOW_ONE_SUB_LE_INV` | Any finite index set. Holds for w_i >= 0 with sum w_i x_i < 1 (upper sign, x_i >= -1) or > -1 (lower sign, x_i <= 1). |
| Young 1 | `YOUNG_INEQUALITY_BOUNDS` | As printed. The right link for x, y >= 0 is HOL Light's `YOUNG_INEQUALITY`. |
| Ky Fan | `KY_FAN_INEQUALITY` | Any finite index set. a_i >= 0 (a_i <= 1 follows), with 0^0 = 1. |
| Mahler | `MAHLER_INEQUALITY` | Any nonempty finite index set; x_i, y_i >= 0. |
| Carleman | `CARLEMAN_INEQUALITY` | As printed (the order of the terms matters, so the index set stays 1..n). |
| Radon | `RADON_INEQUALITY`, `RADON_INEQUALITY_REV` | Any finite index set. For p > 1, x_i = 0 wherever a_i = 0; the reverse for p in [0,1] needs nothing more. |

### Binomials, Stirling and entropy (`binomial_entropy.ml`)

H is `binary_entropy`, -(x ln x + (1-x) ln(1-x))/ln 2, equal to -lg(x^x (1-x)^(1-x)) on
[0,1]; lg x is log x / log 2.

| Entry | Theorems | Remarks |
|---|---|---|
| Binomial 1 | `BINOM_POWER_INEQUALITY`, `BINOM_GE_POW_DIV_POW`, `BINOM_GE_SUB_POW_DIV_FACT`, `BINOM_LE_POW_DIV_FACT`, `POW_DIV_FACT_LE_EXP_POW`, `BINOM_LE_ENTROPY_POW` | The first lower bound needs k <= n; n^k/k! <= (en/k)^k also holds for k = 0 and real x >= 0 in place of n. |
| Binomial 2 | `BINOM_SQRT_INEQUALITY`, `BINOM_SQRT_INEQUALITY_GEN`, `CENTRAL_BINOM_INEQUALITY` | sqrt n >= k is written k^2 <= n, and n^k/k! (1 - k(k-1)/(2n)) <= C(n,k) holds for all n, k. The central bounds hold for n >= 1. |
| Binomial 3 | `BINOM_PRODUCT_INEQUALITY`, `BINOM_SCALING_INEQUALITY`, `BINOM_SCALING_INEQUALITY_GEN` | C(tn,k) >= t^k C(n,k) for every natural t; also m^k C(n,k) <= n^k C(m,k) for n <= m. |
| Binomial 4 | `BINOM_ENTROPY_INEQUALITY`, `BINARY_ENTROPY_RPOW` | alpha is a real a with k = a n, 0 < k < n. |
| Binomial 5 | `BINOM_SUM_INEQUALITY`, `SUM_BINOM_LE_POW_ADD_1`, `SUM_BINOM_LE_EXP_POW`, `SUM_BINOM_LE_POW_2` | d = 0 is included; the second bound needs d <= n. |
| Binomial 6 | `BINOM_TAIL_INEQUALITY`, `SUM_BINOM_LE_RATIO_MUL`, `SUM_BINOM_LE_ENTROPY`, `SUM_BINOM_LE_EXP_SQUARE` | The first bound for a in [0, 1/2), the other two for a <= 1/2. |
| Binary entropy 1 | `BINARY_ENTROPY_UPPER_INEQUALITY`, `BINARY_ENTROPY_LE_MUL_LOG`, `BINARY_ENTROPY_LE_MUL_LOG_ALT`, `BINARY_ENTROPY_LE_RPOW`, `BINARY_ENTROPY_LE_LOG_MUL_LOG` | Holds on the closed interval [0,1]. |
| Binary entropy 2 | `BINARY_ENTROPY_LOWER_INEQUALITY`, `BINARY_ENTROPY_GE_QUADRATIC`, `BINARY_ENTROPY_GE_LOG_MUL_LOG` | Holds on the closed interval [0,1]. |
| Binary entropy 3 | `BINARY_ENTROPY_QUADRATIC_INEQUALITY`, `BINARY_ENTROPY_QUADRATIC_INEQUALITY_GEN` | Holds for \|x\| <= 1/2, and also with 1 - 4x^2 <= H(1/2 - x) <= 1 - (2/ln 2) x^2. |
| Stirling | `STIRLING_INEQUALITY`, `STIRLING_FACT_BOUNDS`, `STIRLING_OUTER_BOUNDS`, `STIRLING_INEQUALITY_COUNTEREXAMPLE`, `FACT_EXP_BOUNDS`, `STIRLING_FACT_LIMIT`, `STIRLING_REMAINDER_LIMIT` | False as printed at n = 1, where e(n/e)^n exceeds the second term and the fourth term exceeds en(n/e)^n. The whole chain holds for n >= 2, the two middle links (the Robbins bounds) and e(n/e)^n <= n! <= en(n/e)^n for n >= 1. The constant sqrt(2 pi) comes from Wallis's product (HOL Light's `Multivariate/gamma.ml`), and n!/(sqrt(2 pi n)(n/e)^n) -> 1 is also proved. |

### Convexity and integrals (`convexity.ml`)

| Entry | Theorems | Remarks |
|---|---|---|
| Jensen (sum form) | `REAL_CONVEX_ON_IMP_JENSEN` (library), `REAL_CONCAVE_ON_IMP_JENSEN` | The convex form is HOL Light's `REAL_CONVEX_ON_IMP_JENSEN`; the concave form is stated with -phi convex. Both need phi on a real interval and a finite index set. |
| Sum & integral | `SUM_INTEGRAL_INEQUALITY`, `REAL_INTEGRAL_LE_SUM_INCREASING`, `SUM_LE_REAL_INTEGRAL_INCREASING` | For any real a with L = a + 1 and U = a + n, n natural; each half holds with monotonicity on its own interval. |
| Cauchy | `CAUCHY_CONVEX_INEQUALITY` | f'(a) and f'(b) are derivatives within [a,b], which covers the one-sided and the two-sided readings. |
| Hermite | `HERMITE_INEQUALITY`, `HERMITE_INEQUALITY_MUL` | Integrability of a convex function is proved, not assumed; the form multiplied by b - a holds for a <= b. |
| Gibbs 1 | `GIBBS_INEQUALITY` | Any finite index set; b_i = 0 forces a_i = 0, and 0 log(0/.) = 0. |
| Gibbs 2 | `GIBBS_INEQUALITY_GEN` | Any finite index set; phi concave on a real interval s, with b_i/a_i in s where a_i > 0; a_i = 0 forces b_i = 0; no sign condition on b_i. Also holds when sum a_i = 0. |
| Pinsker | `PINSKER_INEQUALITY`, `PINSKER_INEQUALITY_LOG` | Any finite index set; b_i = 0 forces a_i = 0, and 0 log(0/.) = 0. Proved in natural logarithms, which is stronger, and in bits. |
| Schur-Vornicu | `SCHUR_VORNICU_INEQUALITY`, `SCHUR_VORNICU_INEQUALITY_GEN` | Every natural k, including k = 0, with no sign condition on x, y, z; f >= 0 and convex or monotone on any set containing them. |
| Young 2 | `YOUNG_INTEGRAL_INEQUALITY`, `YOUNG_INTEGRAL_INEQUALITY_ALT` | f continuous and strictly increasing on [0,c] with f(0) = 0 and g(f(x)) = x there, for 0 <= a <= c and 0 <= b <= f(c); also on [0, infinity) for b in the range of f. |
| Karamata | `KARAMATA_INEQUALITY`, `KARAMATA_INEQUALITY_CONCAVE` | Only b is assumed nonincreasing. |
| Muirhead | `MUIRHEAD_INEQUALITY` | Only b is assumed nonincreasing. Real exponents, with x_i > 0, or x_i >= 0 and a_i >= 0 (0^0 = 1). |

### Series (`series.ml`)

| Entry | Theorems | Remarks |
|---|---|---|
| Hilbert 1 | `HILBERT_INEQUALITY_ABS_FINITE`, `HILBERT_INEQUALITY_FINITE`, `HILBERT_INEQUALITY` | Proved for every finite rectangle with \|a_m b_n\| and no hypotheses. For square-summable a and b the iterated series converge (every inner series, and the outer one) and satisfy the bound. |
| Hilbert 2 | `HILBERT_MAX_INEQUALITY_ABS_FINITE`, `HILBERT_MAX_INEQUALITY_FINITE`, `HILBERT_MAX_INEQUALITY` | Proved for every finite rectangle with \|a_m b_n\| and no hypotheses. For square-summable a and b the iterated series converge (every inner series, and the outer one) and satisfy the bound. |
| Hardy | `HARDY_INEQUALITY_FINITE`, `HARDY_INEQUALITY` | For every partial sum with a_i >= 0, and for series when sum a_n^p converges (the left series then converges). |
| Mathieu | `MATHIEU_INEQUALITY`, `MATHIEU_INEQUALITY_LOWER` | The series converges for every c; the lower bound also holds at c = 0. |

### Moments and tails of one random variable (`probability_basic.ml`, planned)

| Entry | Theorems | Remarks |
|---|---|---|
| Jensen (expectation form) | planned | |
| Chebyshev (expectation form) | planned | |
| Khintchine | deferred | The constant 1/sqrt 2 is Szarek's sharp constant; its proof is research scope. |
| Bonferroni | planned | |
| Bhatia-Davis | planned | |
| Markov 1 | planned | |
| Markov 2 | planned | |
| Markov 3 | planned | |
| Chebyshev 1 | planned | |
| Chebyshev 2 | planned | |
| 2nd moment 1 | planned | |
| 2nd moment 2 | planned | |
| kth moment 1 | planned | |
| 4th moment | planned | |
| Paley-Zygmund | planned | |

### Concentration (`probability_concentration.ml`, planned)

| Entry | Theorems | Remarks |
|---|---|---|
| kth moment 2 | planned | |
| Chernoff 1 | planned | |
| Chernoff 2 | planned | The printed hypotheses are contradictory (X_i in {0,1} and Pr[X_i = ±1] = 1/2); to be stated for independent X_i with E[X_i] = 0 and \|X_i\| <= 1, which covers X_i = ±1 with probability 1/2. |
| Chernoff 3 | planned | |
| Chernoff 4 | planned | |
| Chernoff 5 | planned | |
| Chernoff 6 | planned | |
| Chernoff 7 | planned | |
| Hoeffding | planned | |
| Hoeffding lemma | planned | |
| Bennett | planned | |
| Bernstein | planned | |
| Efron-Stein | planned | |
| McDiarmid | planned | |

### Maximal inequalities, martingales and dependency (`probability_maximal.ml`, planned)

| Entry | Theorems | Remarks |
|---|---|---|
| Kolmogorov | planned | |
| VPG 1 | planned | False when the variance is 0 (a point mass); to be stated for sigma > 0. |
| VPG 2 | planned | |
| VPG 3 | planned | |
| Etemadi | planned | |
| Doob | planned | |
| Azuma | planned | |
| Janson | planned | |
| Lovász 1 | planned | |
| Lovász 2 | planned | |

### Matrices (`matrix.ml`, planned)

| Entry | Theorems | Remarks |
|---|---|---|
| Hadamard | planned | |
| Schur 1 | planned | |
| Schur 2 | planned | |

Distributed with HOL Light under the same license terms.
