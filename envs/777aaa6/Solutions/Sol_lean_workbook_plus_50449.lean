-- Prove2me | solution 1 for lean_workbook_plus_50449
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:33:14.715002+00:00
-- url     : https://prove2.me/submissions/f8f2b116-cf01-4a85-9d10-b85ecd0ee8a2

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
theorem solution : ¬ (∀ n : ℕ, (1 + 1 / (n + 1)) ^ (n + 1) ≥ 2) := by
  intro h
  have hc := h 1
  norm_num at hc <;> grind
