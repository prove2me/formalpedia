-- Prove2me | solution 1 for lean_workbook_plus_58482
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T22:34:35.581918+00:00
-- url     : https://prove2.me/submissions/8321ec07-3725-4a42-80a7-4129f2993dc9

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
theorem solution : ¬ (781 ≡ 1 [ZMOD 71]) := by
  norm_num [Int.ModEq]
