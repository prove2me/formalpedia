-- Prove2me | solution 1 for lean_workbook_plus_72596
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:52.493211+00:00
-- url     : https://prove2.me/submissions/e587fda4-1c76-4eea-a606-6d27b6bf73f8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f g : ℝ → ℝ) (hf : ∃ c, ∀ x, f x = c) (hg : ∀ x, g x = 2013) : ∃ c, ∀ x, f x + g x = c + 2013 := by
  (intros; simp_all)
