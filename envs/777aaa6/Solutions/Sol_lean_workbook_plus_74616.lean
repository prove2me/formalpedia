-- Prove2me | solution 1 for lean_workbook_plus_74616
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:23.123264+00:00
-- url     : https://prove2.me/submissions/422afe83-ea2f-4804-a26e-fc1b27f7c0f6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p q r : Prop) : (p → q ∨ r) ↔ (p → q) ∨ (p → r) := by
  classical
  tauto
