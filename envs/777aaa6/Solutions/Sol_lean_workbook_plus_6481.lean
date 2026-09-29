-- Prove2me | solution 1 for lean_workbook_plus_6481
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:52.873053+00:00
-- url     : https://prove2.me/submissions/1c890d5e-55c5-45ae-b63b-e16374c3778a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ) : a-1 ∈ {x | x^2 - 2*a*x + a^2 - 1 = 0} ∧ a+1 ∈ {x | x^2 - 2*a*x + a^2 - 1 = 0} := by
  intros
  grind
