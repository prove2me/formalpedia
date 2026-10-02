-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_evaluation
-- name    : ZudilinZeta.zudilin_partial_fraction_evaluation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T12:10:48.873461+00:00
-- url     : https://prove2.me/theorems/911b136f-44af-4306-8db2-a6f36e854b6a
-- title:
--   Evaluate Zudilin’s series from finite partial-fraction data
-- statement:
--   For admissible parameters $P$, an integer $n\ge0$, and any partial-fraction datum $d$ for $R_n$, let $A_0$ and $A_s$ denote the finite rational expressions in `ZudilinZetaPartialFractions`. Then
--   $$
--   F_n=A_0+\sum_{k=1}^{(q-r-2)/2} A_{2k+1}\,\zeta(r+2k).
--   $$
--   The datum includes the partial-fraction identity on $t>-1$, the reflection identity, and vanishing of the sum of the simple-pole coefficients. The conclusion retains only the odd zeta values $\zeta(r+2),\ldots,\zeta(q-2)$. This evaluation is valid also for $r=1$, when cancellation of the simple-pole row is necessary for summation. No existence of partial-fraction data and no coefficient-integrality assertion is assumed implicitly.
-- source:
--   W. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, definition of R_n and Lemma 1, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf; W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemma 19 and its proof, pp. 31–33, equations (8.10)–(8.12).

import Definitions.Def_ZudilinZetaPartialFractions

namespace ZudilinZeta

theorem zudilin_partial_fraction_evaluation (P : Params) (n : ℕ) (d : PartialFractionData P n) :
    F P n = (d.constantCoefficient : ℝ) +
      ∑ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2),
        (d.zetaCoefficient (2 * k + 1) : ℝ) * zetaR (P.r + 2 * k) := by sorry

end ZudilinZeta
