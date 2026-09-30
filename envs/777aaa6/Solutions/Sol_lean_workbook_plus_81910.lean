-- Prove2me | solution 1 for lean_workbook_plus_81910
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:19:58.458062+00:00
-- url     : https://prove2.me/submissions/77fd629a-38de-4b85-b864-f9ba713d2a8b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x ^ 2 < 2 → 1 / (4 - x ^ 2) ≤ (x ^ 4 + 5) / 18 := by
  intro x hx
  apply (div_le_iff₀ (show 0 < 4 - x ^ 2 by linarith)).2
  have hs := mul_nonneg (show 0 ≤ 2 - x ^ 2 by linarith) (sq_nonneg (x ^ 2 - 1))
  nlinarith [hs]
