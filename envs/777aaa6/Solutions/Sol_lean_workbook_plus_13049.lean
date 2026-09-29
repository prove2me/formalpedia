-- Prove2me | solution 1 for lean_workbook_plus_13049
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:50.582811+00:00
-- url     : https://prove2.me/submissions/e17b03c5-7d56-48a7-89c9-4ffbf7d98592

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ b c : ℝ, (b * c ≠ 0 → 1 / b ^ 2 + 1 / c ^ 2 ≥ 2 / (b * c)) := by
  intro b c h
  rcases mul_ne_zero_iff.mp h with ⟨hb,hc⟩
  have hi : 1/b^2+1/c^2-2/(b*c)=(b-c)^2/(b^2*c^2) := by field_simp; ring
  have hp : 0≤(b-c)^2/(b^2*c^2) := by positivity
  linarith
