-- Prove2me | solution 1 for lean_workbook_plus_41791
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:27.246257+00:00
-- url     : https://prove2.me/submissions/aa6a9313-7a13-4c2b-8dca-bc1c3cff96cc

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
theorem solution : ¬ (¬(9 * 2 ^ 511 + 1) % 2 = 1) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  omega
