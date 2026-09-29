-- Prove2me | solution 1 for lean_workbook_plus_59550
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:34:13.633081+00:00
-- url     : https://prove2.me/submissions/d49729a3-ee56-4d0a-9b58-6565d621e154

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a : ℝ) (hf: f = fun x ↦ x^2 + a) : (∀ x, f x = x^2 + a) := by
  (intros; simp_all)
