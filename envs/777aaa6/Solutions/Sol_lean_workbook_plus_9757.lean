-- Prove2me | solution 1 for lean_workbook_plus_9757
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:41.32473+00:00
-- url     : https://prove2.me/submissions/7223bcf2-6c90-474d-a357-f8be7be440b3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f x = 2 * x) : f x = 2 * x := by
  (intros; simp_all)
