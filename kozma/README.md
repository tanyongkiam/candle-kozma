# Inequalities from Kozma's "Useful Inequalities"

Formal proofs of inequalities from László Kozma's sheet "Useful
Inequalities" (version 0.44).

  finite_sums.ml   Inequalities about finite sums and products of reals

To load:

  needs "kozma/finite_sums.ml";;

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
  - Only the first part of Chong's inequality and the cases n = 3, 4 of
    Shapiro's inequality are proved.

Distributed with HOL Light under the same license terms.
