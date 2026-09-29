-- Prove2me | solution 1 for lean_workbook_plus_33810
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:50.724926+00:00
-- url     : https://prove2.me/submissions/cb55fe97-83b7-428e-922b-f4162dac62e0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a c : ℤ) (h1 : Odd a) (h2 : Odd c) : Even (a + c) := by
  intros
  grind
