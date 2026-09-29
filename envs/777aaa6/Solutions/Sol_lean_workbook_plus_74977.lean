-- Prove2me | solution 1 for lean_workbook_plus_74977
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:51.645307+00:00
-- url     : https://prove2.me/submissions/f165ddb3-ae3e-4835-9d85-415f4bba12d0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x : ℝ) (hf: f x = if x ≤ 0 then 0 else 1) : f x = if x ≤ 0 then 0 else 1 := by
  (intros; simp_all)
