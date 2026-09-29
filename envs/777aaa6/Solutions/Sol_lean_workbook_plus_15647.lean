-- Prove2me | solution 1 for lean_workbook_plus_15647
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:00:56.011608+00:00
-- url     : https://prove2.me/submissions/fbe8137d-ea0a-490f-8a46-08298276fe22

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (h1: a ≤ b ∧ b ≤ c ∧ c ≤ d) (h2: b + c = a + d) : b * c ≥ a * d := by
  rcases h1 with ⟨hab,hbc,hcd⟩
  nlinarith [congrArg (fun t : ℝ => a*t) h2, mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ c-a by linarith)]
