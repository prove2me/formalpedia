-- Prove2me | solution 1 for lean_workbook_plus_38113
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:44.765344+00:00
-- url     : https://prove2.me/submissions/cadf36f3-c0ff-4a41-b0c1-f8219e6bb2c9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f = fun x => if x = 0 then 0 else 1) : f x = if x = 0 then 0 else 1 := by
  (intros; simp_all)
