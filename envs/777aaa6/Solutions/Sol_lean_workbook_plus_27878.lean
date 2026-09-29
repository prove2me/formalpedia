-- Prove2me | solution 1 for lean_workbook_plus_27878
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:41.982302+00:00
-- url     : https://prove2.me/submissions/43995afe-7127-4d7f-af28-dec49c840c08

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ≥ b ∧ b ≥ c ∧ c ≥ 0 → (b + c) / (a ^ 2 + b * c) + (c + a) / (b ^ 2 + c * a) + (a + b) / (c ^ 2 + a * b) ≥ 9 / (a + b + c)) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨(9), ?_⟩
  norm_num at *
  refine ⟨(9), ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
