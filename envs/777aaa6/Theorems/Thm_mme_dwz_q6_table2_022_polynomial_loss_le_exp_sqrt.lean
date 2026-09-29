-- Prove2me | Theorems.Thm_mme_dwz_q6_table2_022_polynomial_loss_le_exp_sqrt
-- name    : mme_dwz_q6_table2_022_polynomial_loss_le_exp_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:50:17.040428+00:00
-- url     : https://prove2.me/theorems/72a3fdd1-1b0f-4fe8-a767-d56bbec0891c
-- title:
--   Square-root exponential absorption of the 022/202 method-of-types loss
-- statement:
--   For every integer $m\geq 0$ and real $\tau\geq 0$, prove the explicit uniform estimate
--
--   $$
--   (6(m+1))^{3\tau}\leq\exp\!\left(155520\,\tau\sqrt{m+1}\right).
--   $$
--
--   This converts the degree-three finite method-of-types loss in the $022/202$ dimension estimate into a square-root exponential. Such a loss is subexponential and can therefore be absorbed by any strict gap below the limiting component base.
-- source:
--   Standard exponential-series estimate applied to the explicit method-of-types loss arising in Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.3; https://arxiv.org/abs/2210.10173.

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false

theorem mme_dwz_q6_table2_022_polynomial_loss_le_exp_sqrt
    (tau : ℝ) (htau : 0 ≤ tau) (m : ℕ) :
    ((6 * (((m + 1 : ℕ) : ℝ))) ^ 3) ^ tau ≤
      Real.exp ((155520 * tau) *
        Real.sqrt (((m + 1 : ℕ) : ℝ))) := by
  sorry
