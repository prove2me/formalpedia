-- Prove2me | solution 1 for lean_workbook_plus_24347
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:09.768646+00:00
-- url     : https://prove2.me/submissions/68a5fcf8-4e0f-4f78-bf3f-091086c72232

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => -x-1) : ∀ x ∈ Set.Icc (-1) 1, f x = -x-1 := by
  (intros; simp_all)
