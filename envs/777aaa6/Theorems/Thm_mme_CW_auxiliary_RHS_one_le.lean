-- Prove2me | Theorems.Thm_mme_CW_auxiliary_RHS_one_le
-- name    : mme_CW_auxiliary_RHS_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:30:56.973294+00:00
-- url     : https://prove2.me/theorems/3e14d6dc-ae38-4776-a131-96e24eb2c986
-- title:
--   The normalized CW auxiliary value is at least one
-- statement:
--   For positive normalized Section-8 frequencies, the CW auxiliary value is at least one. The five denominator bases from equation (13),
--
--   $$
--   2a+2b+c,\quad 2b+2d,\quad 2c+d,\quad 2b,\quad a,
--   $$
--
--   are positive and sum to one, so every factor $x^x$ in the denominator is at most one. When $q\ge3$ and $3\tau\ge2$, every numerator base is at least one and every numerator exponent is nonnegative.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (11)--(13) and normalized auxiliary expression on journal pp. 268--269 (PDF pp. 18--19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
open MME Real

theorem mme_CW_auxiliary_RHS_one_le
    (q : ℕ) (hq : 3 ≤ q)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnorm : 3 * a + 6 * b + 3 * c + 3 * d = 1) :
    1 ≤ auxiliaryRHS q tau a b c d := by sorry
