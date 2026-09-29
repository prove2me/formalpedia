-- Prove2me | solution 1 for lean_workbook_plus_71808
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:44.444759+00:00
-- url     : https://prove2.me/submissions/d7930878-9a0e-454a-bf6f-b653fdfc1681

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a^4 + 2*a^2*b^2 + b^4 + a^2*c^2 + 2*a*b*c^2 + b^2*c^2 ≥ 2*a^3*c + 2*a*b*c^2 + 2*b^3*c + 2*a*b^2*c) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
