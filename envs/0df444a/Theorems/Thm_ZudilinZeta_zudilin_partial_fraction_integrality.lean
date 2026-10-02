-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_integrality
-- name    : ZudilinZeta.zudilin_partial_fraction_integrality
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T12:11:25.691984+00:00
-- url     : https://prove2.me/theorems/955bbaac-186b-42f9-b221-e1fe1660855b
-- title:
--   Denominator estimates for the explicit partial-fraction coefficients
-- statement:
--   Let $P$ be admissible, $n>0$, and let $d$ be any partial-fraction datum for $R_n$. Let $A_0$ be its finite harmonic constant and $A_s$ its coefficient of $\zeta(s+r-1)$, as defined in `ZudilinZetaPartialFractions`. With
--   $$
--   Q_n=\frac{D_{m_1n}^{r}\prod_{j=2}^{q-r}D_{m_jn}}{\Phi_n},
--   $$
--   one has
--   $$
--   Q_nA_0\in\mathbb Z,\qquad
--   Q_nA_{2k+1}\in\mathbb Z\quad\left(1\le k\le\frac{q-r-2}{2}\right).
--   $$
--   All quantities in these inclusions are rational numbers given by finite sums and products. This isolates the arithmetic denominator estimates for the canonical coefficients; it asserts neither an infinite-series evaluation nor irrationality.
-- source:
--   W. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, definition of R_n and Lemma 1, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf; W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemma 19 and its proof, pp. 31–33, equations (8.10)–(8.12).

import Definitions.Def_ZudilinZetaPartialFractions

namespace ZudilinZeta

theorem zudilin_partial_fraction_integrality (P : Params) (n : ℕ) (hn : 0 < n)
    (d : PartialFractionData P n) :
    (∃ a : ℤ, denominatorScale P n * d.constantCoefficient = (a : ℚ)) ∧
      ∀ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2),
        ∃ a : ℤ, denominatorScale P n * d.zetaCoefficient (2 * k + 1) = (a : ℚ) := by sorry

end ZudilinZeta
