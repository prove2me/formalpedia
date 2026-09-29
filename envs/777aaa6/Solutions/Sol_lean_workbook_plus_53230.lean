-- Prove2me | solution 1 for lean_workbook_plus_53230
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:28.667717+00:00
-- url     : https://prove2.me/submissions/df3e05f0-6cfd-4461-a84f-9438b3bfd6a1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (y : ℝ) : 3*y - 7 < 2*y + 1 ↔ y < 8 := by
  intros
  grind
