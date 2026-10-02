-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_constant_shift
-- name    : ZudilinZeta.zudilin_partial_fraction_constant_shift
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T13:51:32.549296+00:00
-- url     : https://prove2.me/theorems/06630671-5ed6-4a7b-860e-10bb5249fbd2
-- title:
--   Shift the finite harmonic constant to the first numerator zero
-- statement:
--   For admissible parameters $P$, $n>0$, and any partial-fraction datum for $R_n$, the constant obtained from the series starting at $t=0$ equals its shifted finite expression:
--   $$
--   -\sum_{s=1}^{q-r}w_s\sum_{k\in K}c_{s,k}\sum_{l=1}^{k-1}l^{-(s+r-1)}
--   =
--   -\sum_{s=1}^{q-r}w_s\sum_{k\in K}c_{s,k}\sum_{l=1}^{k-h_1}l^{-(s+r-1)}.
--   $$
--   Here $w_s=s^{\overline{r-1}}/(r-1)!$ and $K$ is the full pole interval. The reason is that extending the rational derivative series down to $1-h_1$ adds only zeros: each added integer is a numerator zero of order at least $r$. At negative integers this argument uses the polynomial/rational continuation obtained by canceling the Gamma quotients, not pointwise differentiation of their total real-valued quotient at Gamma poles.
-- source:
--   W. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, R_n and Lemma 1, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf; Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemmas 15–19, pp. 27–33, especially (8.10)–(8.12).

import Definitions.Def_ZudilinZetaCoefficientArithmetic

namespace ZudilinZeta

theorem zudilin_partial_fraction_constant_shift (P : Params) (n : ℕ) (hn : 0 < n)
    (d : PartialFractionData P n) :
    d.constantCoefficient = d.shiftedConstantCoefficient := by sorry

end ZudilinZeta
