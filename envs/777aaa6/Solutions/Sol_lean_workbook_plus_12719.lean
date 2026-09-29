-- Prove2me | solution 1 for lean_workbook_plus_12719
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:58.240593+00:00
-- url     : https://prove2.me/submissions/b8885806-4cb5-4271-933c-49f0059778a2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y : ℤ, x^2 + x = y^2 + y ↔ (x - y) * (x + y + 1) = 0 := by
  intro x y
  intros
  grind
