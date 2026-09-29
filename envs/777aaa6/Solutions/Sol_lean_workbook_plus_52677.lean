-- Prove2me | solution 1 for lean_workbook_plus_52677
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:25.688716+00:00
-- url     : https://prove2.me/submissions/533ec302-e2ea-468c-a261-b51b2899f27e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y p q : ℝ) : x - y = p ∧ x + y - 1 = q ↔ x = (p + q + 1) / 2 ∧ y = (q - p + 1) / 2 := by
  intros
  grind
