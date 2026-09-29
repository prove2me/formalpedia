-- Prove2me | solution 1 for lean_workbook_plus_44892
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:29.903307+00:00
-- url     : https://prove2.me/submissions/92db528c-c8dd-42cf-ad26-77e1006784f6

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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x : ℝ)
  (h₀ : 82 / 85 = x / 100), x = 96.47) := by
  intro h
  have hc := h (1640 / 17) (by norm_num)
  clear h
  norm_num at hc <;> grind only []
