# Inequalities from Kozma's "Useful Inequalities"

Formal proofs of inequalities from László Kozma's sheet "Useful
Inequalities" (version 0.44).

  finite_sums.ml     Inequalities about finite sums and products of reals
  combinatorics.ml   Inequalities about finite set systems and prefix-free codes
  bernoulli_exp.ml   Bernoulli's inequality and bounds on the exponential
  log_trig_sqrt.ml   Bounds on the logarithm, trigonometric and hyperbolic
                     functions and square roots
  means.ml           Inequalities between means and weighted products
  binomial_entropy.ml  Binomial coefficients, Stirling's formula and the
                     binary entropy

To load all files:

  needs "kozma/make.ml";;

Deviations from the sheet:

  - Sums and products over 1..n are generalized to any finite index set
    where the order of the terms does not matter (Cauchy-Schwarz,
    Kantorovich, Milne, Chebyshev, the first sum & product inequality).
  - Chebyshev's sum inequality does not assume x_1 <= ... <= x_n.
  - Nesbitt: the terms a_i / (S - a_i) are undefined when a_i = S, so
    a_i < S is assumed; a_i >= 0 is not needed. In Milne a term with
    a_i + b_i = 0 has value 0.
  - Kantorovich does not assume x_i, y_i > 0; 0 < m <= x_i / y_i <= M
    suffices.
  - Abel: the minimum and maximum of the partial sums are written as
    inf and sup of the (finite) set of partial sums, for n >= 1.
  - Aczel's inequality is split by the two alternative hypotheses, which
    are relaxed to non-strict ones. Samuelson's two bounds are combined
    into one bound on |x_i - mu|.
  - Only the cases n = 3, 4 of Shapiro's inequality are proved.
  - Chong: the second part is in means.ml, over any finite index set and
    for a_i >= 0 (with 0^0 = 1).
  - Means (means.ml): sums and products range over any finite index set,
    except in Carleman's inequality. Hölder is HOELDER_SUM_INEQUALITY with
    p, q > 0, 1/p + 1/q = 1; Heinz holds for x, y >= 0; Mahler for
    x_i, y_i >= 0 and a nonempty index set; Ky Fan for a_i >= 0 (a_i <= 1
    follows) with 0^0 = 1.
  - Means 1 and 2: min and max are inf and sup of the finite set of values.
    The chain of means 1 holds for x_i > 0, its links from GM on for
    x_i >= 0, AM <= QM for all real x_i; means 2 needs y_i <> 0 and is also
    proved as the mediant inequality for real a_i and b_i > 0.
  - Power means: M_p is power_mean, with M_0 = prod |x_i|^w_i; for p < 0,
    x_i <> 0 wherever w_i > 0. The printed limits min x_i and max x_i are
    false (x = (-2, 1), w = (1/2, 1/2)); the limits are min and max of |x_i|
    over w_i > 0, and the limit at 0 holds from the right for every x.
  - Lehmer: for p < 1, x_i <> 0 wherever w_i > 0. The log mean chain
    assumes x <> y; its outer links hold for x, y >= 0. Radon: for p > 1,
    x_i = 0 wherever a_i = 0; the reverse for p in [0,1] needs nothing more.
  - Weierstrass: the right link of the second line holds for x_i in [-1,1)
    and w_i >= 0, the third line for w_i >= 0 with sum w_i x_i < 1 (upper
    sign, x_i >= -1) or > -1 (lower sign, x_i <= 1); the left link of the
    second line holds for all x_i >= 0.
  - Maclaurin-Newton: S_k is symmetric_mean (the mean over k-subsets).
    Newton holds for all real a_i and every k >= 1; Maclaurin for every
    k >= 1 and a_i >= 0.
  - Kraft: the leaves of a binary tree are modelled as a prefix-free set of
    words (a leaf's depth is the length of its word). The inequality is
    proved for every prefix-free set of words over any finite alphabet; for
    an infinite prefix-free set it applies to every finite subset.
  - LYM: antichains of subsets of any finite set instead of {1, ..., n}.
  - FKG: "monotone" is read as both increasing or both decreasing; the two
    cases are separate theorems, over any finite ground set.
  - Shearer: false as printed when A is empty, t = 0 and the family is
    nonempty (1 <= 0). This case is excluded and the printed form is
    refuted. Proved over any finite ground set, for any finite family,
    including families with repeated sets; the members need not be subsets
    of the ground set.
  - Sauer-Shelah: str(A) is the set of shattered sets and vc(A) its largest
    size. The chain holds for every set system over a finite ground set,
    including the empty set system, for which vc is not defined.
  - Bernoulli: (1 + x)^r is undefined at x = -1 for r < 0, which is
    excluded; x < 1/r is written r x < 1, and the second inequality
    holds for r >= 0 and for r <= -1. The third holds for all x > -1,
    the fifth whenever (n + 1) x >= -1 and for every x when n is odd,
    and the sixth includes n = 0.
  - Exponential: the first line holds for x >= -n (real n >= 1), the
    second for x >= 0, with n a natural number >= 1 in the n! bound and
    real n > 0 elsewhere. e^(2x) <= (1 + x)/(1 - x) holds on [0, 1),
    and the first bound of the fifth line for x >= 0 with r >= 1 and
    for x > 0 with r < 0. The bounds of the seventh line hold up to any
    threshold where they hold at the threshold; e^x <= 1 + x + x^2 is
    stated for x <= 1.79. The five sign cases of the last line are
    covered, with their boundary cases, by three theorems.
  - Exponential: x^y > x / (x + y) is false for x = 1/2, y = 4. The
    printed form is refuted and the inequality is proved for y <= 1 or
    x >= 1.
  - Logarithm: ln(1 + x)/x is undefined at x = 0, so the two links that
    contain it assume x <> 0. The first two links of the third line hold
    for every real n > 0. In the fourth line, |ln x| <= |x - 1/x|/2 needs
    only x > 0, and ln(x + y) <= ln x + y/x only x > 0 and x + y > 0.
  - Trigonometric and hyperbolic: the condition x in [0, pi/2] printed at
    the end of the second hyperbolic line is applied to all three lines.
    sinh x is written (e^x - e^-x)/2 and the cube root as root 3. At x = 0
    the terms x^3/sinh^2 x and x^2/sinh x are 0. sin x / x is undefined at
    0 and tan x at pi/2, so the second hyperbolic line assumes x > 0 and
    its last link x < pi/2; it is also proved multiplied by x on the closed
    interval. x cos^2(x/2) <= sin x and sin x <= x cos(x/2) hold on
    [0, pi], and sin x <= (x cos x + 2x)/3 for all x >= 0.
  - Binomial (binomial_entropy.ml): the first lower bound of Binomial 1
    needs k <= n; n^k/k! <= (en/k)^k also holds for k = 0 and real x >= 0
    in place of n. sqrt n >= k is written k^2 <= n, and n^k/k! (1 -
    k(k-1)/(2n)) <= C(n,k) holds for all n, k. The central bounds of
    Binomial 2 hold for n >= 1. Binomial 3: C(tn,k) >= t^k C(n,k) for every
    natural t. Binomial 4: alpha is a real a with k = a n, 0 < k < n.
    Binomial 5: d = 0 is included; the second bound needs d <= n. Binomial
    6: the first bound for a in [0, 1/2), the other two for a <= 1/2.
  - Binary entropy: H is binary_entropy, -(x ln x + (1-x) ln(1-x))/ln 2,
    equal to -lg(x^x (1-x)^(1-x)) on [0,1]; lg x is log x / log 2. All
    bounds hold on the closed interval [0,1]; the third line holds for
    |x| <= 1/2, and also with 1 - 4x^2 <= H(1/2 - x) <= 1 - (2/ln 2) x^2.
  - Stirling: false as printed at n = 1, where e(n/e)^n exceeds the
    second term and the fourth term exceeds en(n/e)^n. The whole chain
    holds for n >= 2, the two middle links (the Robbins bounds) and
    e(n/e)^n <= n! <= en(n/e)^n for n >= 1.

Distributed with HOL Light under the same license terms.
