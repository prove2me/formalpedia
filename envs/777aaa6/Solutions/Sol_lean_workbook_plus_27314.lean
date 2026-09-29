-- Prove2me | solution 1 for lean_workbook_plus_27314
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:22:21.521043+00:00
-- url     : https://prove2.me/submissions/e19a8dc6-f490-449b-a414-f3eb981bf514

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
set_option autoImplicit false
set_option maxHeartbeats 500000
theorem solution (f : ℝ → ℝ) (hf : ∀ x y, f (x * f y + y * f x) = x ^ 2 + y ^ 2) : ∃ k, ∀ x, f x = k * x ∨ ∀ x, f x = k / x   :=  by
  have h0 : f 0 = 0 := by simpa using hf 0 0
  have h1 : f 0 = 1 := by simpa [h0] using hf 1 0
  norm_num [h0] at h1
#print axioms solution
