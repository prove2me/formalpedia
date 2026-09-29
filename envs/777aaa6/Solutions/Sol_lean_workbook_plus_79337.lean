-- Prove2me | solution 1 for lean_workbook_plus_79337
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:04:41.189979+00:00
-- url     : https://prove2.me/submissions/2e2a3f0f-1c74-4485-be4b-c91ba8c4d0d1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (n : ℤ), ⌊n⌋ + 1 = ⌈n⌉) := by
  push_neg
  norm_num at *
