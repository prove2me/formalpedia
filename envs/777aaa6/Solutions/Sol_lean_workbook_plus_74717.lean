-- Prove2me | solution 1 for lean_workbook_plus_74717
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:41:02.387006+00:00
-- url     : https://prove2.me/submissions/284be3ad-2183-47a8-8e6b-2c1a94707e13

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (2*x*y/((z+x)*(z+y)) + 2*y*z/((x+y)*(x+z)) + 3*z*x/((y+z)*(x+y)) ≥ 5/3 ↔ x*(y-2*z)^2 + y*(z-x)^2 + z*(2*x-y)^2 ≥ 0)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
