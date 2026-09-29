-- Prove2me | solution 1 for lean_workbook_plus_59566
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:34:11.144414+00:00
-- url     : https://prove2.me/submissions/260c847c-98b5-4f2d-91ef-50fc3edc9ae9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a : ℝ) (hf: f = fun x => x + a) : (∀ x, f x = x + a) ∧ (∀ x y, f x = f y → x = y) := by
  (intros; simp_all)
