-- Prove2me | solution 1 for lean_workbook_plus_60054
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:04:23.833463+00:00
-- url     : https://prove2.me/submissions/4daafb5a-9817-4ed1-94d0-1f63dde49975

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℤ, x^3 + y^3 + z^3 - 3*x*y*z = (x*y*z)*(x^2 + y^2 + z^2) + (x + y + z)*(-x*y - y*z - z*x)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
