-- Prove2me | solution 1 for lean_workbook_plus_54181
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:10.127207+00:00
-- url     : https://prove2.me/submissions/0a1fd3b2-f97a-4842-8c6e-148f31a71947

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = c) : ∃ c, ∀ x, f x = c := by
  (intros; simp_all)
