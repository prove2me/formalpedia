-- Prove2me | solution 1 for lean_workbook_plus_30204
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:25.699719+00:00
-- url     : https://prove2.me/submissions/630336f6-7ccf-41a7-a3f6-adb24aa258e0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => 1 / Real.sqrt x) : f = fun x => 1 / Real.sqrt x := by
  (intros; simp_all)
