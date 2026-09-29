-- Prove2me | solution 1 for lean_workbook_plus_59268
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:42.939768+00:00
-- url     : https://prove2.me/submissions/a45f5fbd-63e3-4cca-b83f-f839894bd21f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (P S : ℂ) : S^2 - 2 * P = 1 ↔ P = (S^2 - 1) / 2 := by
  intros
  grind
