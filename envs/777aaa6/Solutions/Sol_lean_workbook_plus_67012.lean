-- Prove2me | solution 1 for lean_workbook_plus_67012
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:45.467373+00:00
-- url     : https://prove2.me/submissions/cb58c116-ff96-48ba-ba95-10efb13c92cf

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
theorem solution : ¬ (∀ (h₁ : 4 ≤ 4 ∧ 4 ≤ 5 ∧ 4 ≤ 6 ∧ 4 ≤ 7 ∧ 4 ≤ 8), (Nat.choose 4 4 + Nat.choose 5 4 + Nat.choose 6 4 + Nat.choose 7 4 + Nat.choose 8 4) = 112) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  grind
