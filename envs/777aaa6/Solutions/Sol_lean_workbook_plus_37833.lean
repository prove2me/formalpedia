-- Prove2me | solution 1 for lean_workbook_plus_37833
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:49.920701+00:00
-- url     : https://prove2.me/submissions/537ab230-e015-42af-b9a5-39de34f5a8b5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (y z a : ℂ)
  (h₀ : y^2 = a)
  (h₁ : z^3 = a) :
  (y / z)^6 = a := by
  intros
  grind
