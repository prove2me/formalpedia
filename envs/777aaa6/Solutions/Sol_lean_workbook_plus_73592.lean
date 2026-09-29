-- Prove2me | solution 1 for lean_workbook_plus_73592
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:08:30.007386+00:00
-- url     : https://prove2.me/submissions/19ac9ac3-febb-4ba6-8295-6e43eac17e3f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a : ℝ, 1 + a^2 + a^4 ≥ 1 / (3 * a^2) * (a + a^2 + a^3)) := by
  push_neg
  norm_num at *
  refine ⟨ (    1  /  3  ) , ?_⟩
  norm_num at *
