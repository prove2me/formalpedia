-- Prove2me | solution 1 for lean_workbook_plus_50001
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:43.671384+00:00
-- url     : https://prove2.me/submissions/2297866d-c4f5-46c2-a0a7-4fde4af13f7f

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
theorem solution : ¬ (∀ (s : ℝ)
  (h₀ : s = (2^4 - 1) + 2 * (3^4 - 2^4) + 3 * (4^4 - 3^4) + 4 * (5^4 - 4^4) + 5 * (6^4 - 5^4) + 6 * (2006 - 6^4)), s = 9781) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  grind
