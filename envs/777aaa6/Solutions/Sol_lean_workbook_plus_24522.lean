-- Prove2me | solution 1 for lean_workbook_plus_24522
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:48:36.182508+00:00
-- url     : https://prove2.me/submissions/7c53a493-35c1-4eb2-ab30-dbe52500d872

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ p q : ℝ, (2 * (p + q) ≥ 4 * Real.sqrt (p * q) ∧ p ^ 2 ≥ 3 * q)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
