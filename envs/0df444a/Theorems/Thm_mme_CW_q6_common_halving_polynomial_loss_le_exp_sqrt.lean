-- Prove2me | Theorems.Thm_mme_CW_q6_common_halving_polynomial_loss_le_exp_sqrt
-- name    : mme_CW_q6_common_halving_polynomial_loss_le_exp_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:43:54.594206+00:00
-- url     : https://prove2.me/theorems/781a466a-1c8b-4a1a-be16-e014a2200716
-- title:
--   The common-halving polynomial loss is absorbed by a square-root exponential
-- statement:
--   For every nonnegative integer $N$, the explicit common-halving extraction loss obeys
--
--   $$128(N+1)^{20}\leq\exp\bigl((128\cdot40!)\sqrt{N+1}\bigr).$$
--
--   Thus the full polynomial loss can be absorbed into the square-root exponential term already present in the primary-hash capacity estimate, without changing its asymptotic form.
-- source:
--   Elementary exponential-series estimate, used with the polynomial common-halving loss in the Duan-Wu-Zhou q=6 paired analysis.

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false

theorem mme_CW_q6_common_halving_polynomial_loss_le_exp_sqrt (N : ℕ) :
    (((128 * (N + 1) ^ 20 : ℕ) : ℝ)) ≤
      Real.exp ((128 * ((40 : ℕ).factorial : ℝ)) *
        Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  sorry
