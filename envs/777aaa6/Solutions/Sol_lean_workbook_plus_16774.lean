-- Prove2me | solution 1 for lean_workbook_plus_16774
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:48.125802+00:00
-- url     : https://prove2.me/submissions/f9179a2b-a731-4fec-91f8-2f30c7eed344

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ) (h : a^2 = 1 + a) : a = (1 + Real.sqrt 5) / 2 ∨ a = (1 - Real.sqrt 5) / 2 := by
  intros
  grind
