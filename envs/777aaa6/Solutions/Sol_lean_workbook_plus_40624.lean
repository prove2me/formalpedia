-- Prove2me | solution 1 for lean_workbook_plus_40624
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:32.548546+00:00
-- url     : https://prove2.me/submissions/a1b8dfc8-d425-44f0-b63a-ecccf5367ed2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (R : Type*) [CommRing R]
  (A B : Matrix (Fin 2) (Fin 2) R) :
  A * B ^ 2 - A * B * A = 0 ↔ A * B ^ 2 = A * B * A := by
  intros
  grind
