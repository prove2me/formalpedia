-- Prove2me | solution 1 for lean_workbook_plus_5754
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:13.945757+00:00
-- url     : https://prove2.me/submissions/92809eb0-4ef5-402c-8366-577c8dccb571

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p : ℝ) : 36 + 2 * (p ^ 3 / 3) ≥ 18 * p ↔ (p - 3) ^ 2 * (p + 6) ≥ 0 := by
  intros
  grind
