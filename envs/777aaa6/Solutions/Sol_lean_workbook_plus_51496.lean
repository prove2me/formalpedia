-- Prove2me | solution 1 for lean_workbook_plus_51496
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:19:09.657515+00:00
-- url     : https://prove2.me/submissions/b2bdfc34-5a76-47f5-b7c0-1fe1c842f940

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : x * (x - 3) = -1) : x ^ 3 * (x ^ 3 - 18) = -1 := by
  intros
  grind
