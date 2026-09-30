-- Prove2me | Theorems.Thm_RybinAI2026_P01_diagonal_pair_contraction_from_envelopes
-- name    : RybinAI2026.P01.diagonal_pair_contraction_from_envelopes
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T00:59:18.856434+00:00
-- url     : https://prove2.me/theorems/5bb103dd-3b42-4dba-be22-e981a6303b0b
-- title:
--   Scalar diagonal pair bound from ratio envelopes
-- statement:
--   The two branchwise ratio envelopes from the aligned diagonal 2D proof imply the squared pair-contraction inequality. In the low branch the square-root prefactors suffice; in the high branch the accepted scalar coefficient bound controls the common rational envelope.
-- source:
--   Scalar assembly leaf from the exact two-branch proof of aligned_diagonal_pair_contraction for RybinAI2026.P01.matrix_integral_inequality. The source is artifacts/p01_slack/2026-09-29-no-w-pair.md, Addendum: aligned 2D pair contraction resolved, and it consumes the already-Proved coefficient lemma.

import Mathlib
import Theorems.Thm_RybinAI2026_P01_diagonal_pair_coefficient_bound

theorem RybinAI2026.P01.diagonal_pair_contraction_from_envelopes {x y A B z r s : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ^ 2 = x * (1 - y)) (hB : B ^ 2 = y * (1 - x))
    (hz : 0 ≤ z) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hlow : x + y ≤ 1 → r ^ 2 ≤ A ^ 2 ∧ s ^ 2 ≤ B ^ 2)
    (hhigh : 1 < x + y →
      r ≤ (x + A * z) / (1 + z) ∧ s ≤ (B + y * z) / (1 + z)) :
    r ^ 2 + s ^ 2 ≤ 1 := by
  sorry
