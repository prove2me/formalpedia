-- Prove2me | solution 1 for lean_workbook_plus_64102
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:56.323309+00:00
-- url     : https://prove2.me/submissions/17c2932f-d45e-4c34-abc0-c66ca9979eaa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : 4 * x + (x / 2) * (4 + (x - 1) / 2) = 72), x^2 - x - 48 = 0) := by
  push_neg
  refine ⟨9, ?_⟩
  norm_num <;> grind
