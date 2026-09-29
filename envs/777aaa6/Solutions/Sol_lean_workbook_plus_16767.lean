-- Prove2me | solution 1 for lean_workbook_plus_16767
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:32.705907+00:00
-- url     : https://prove2.me/submissions/3ed8753e-8702-4196-a6a2-ce87ded021f9

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
theorem solution : ¬ (∀ x y z : ℝ, ∀ t : ℕ, x^(t + 1) * (y - z)^2 + y^(t + 1) * (z - x)^2 + z^(t + 1) * (x - y)^2 ≥ 1 / 2 * (x^t + y^t + z^t) * (x + y - 2 * z) * (y + z - 2 * x) * (z + x - 2 * y)) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  grind
