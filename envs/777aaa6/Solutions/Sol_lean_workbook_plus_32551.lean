-- Prove2me | solution 1 for lean_workbook_plus_32551
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:45.946951+00:00
-- url     : https://prove2.me/submissions/2f797b60-73fd-4d80-ad33-17ca23cdc509

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ¬ ∃ a b : ℕ, (a : ℝ) / b = Real.sqrt 2 := by
  rintro ⟨a,b,h⟩
  apply irrational_sqrt_two
  refine ⟨(a:ℚ)/b,?_⟩
  simpa only [Rat.cast_div,Rat.cast_natCast] using h
