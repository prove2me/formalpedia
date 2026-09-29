-- Prove2me | solution 1 for lean_workbook_plus_50206
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:19.437871+00:00
-- url     : https://prove2.me/submissions/a56d8aa0-9c3b-417b-9740-45532b90af4a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 + x - 3/4 = 0 ↔ x = 1/2 ∨ x = -3/2 := by
  intros
  grind
