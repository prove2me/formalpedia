-- Prove2me | solution 1 for lean_workbook_plus_2950
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:31.638719+00:00
-- url     : https://prove2.me/submissions/d6a590b1-297a-4889-a00e-780a8713ce4e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) :
  (a + b + c) ^ 3 ≥ (9 / 4) * (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) ↔
    4 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * (a * (b ^ 2 + c ^ 2) + b * (c ^ 2 + a ^ 2) + c * (a ^ 2 + b ^ 2)) ≥
      30 * a * b * c := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
