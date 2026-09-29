-- Prove2me | solution 1 for lean_workbook_plus_74718
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:59.669694+00:00
-- url     : https://prove2.me/submissions/acf942d6-0ac2-4fdb-a2e2-6836f2f074ff

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y : ℝ, x^3 + y^3 = 2 → x + y ≤ 2 := by
  intro x y
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
