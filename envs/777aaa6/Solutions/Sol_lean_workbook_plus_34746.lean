-- Prove2me | solution 1 for lean_workbook_plus_34746
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:09.081593+00:00
-- url     : https://prove2.me/submissions/80f0728c-c46b-4747-a5a5-d2cbd2994724

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2 ≥ 0 := by
  (intros; positivity)
