-- Prove2me | solution 1 for lean_workbook_plus_53584
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:08.59537+00:00
-- url     : https://prove2.me/submissions/db703b9e-1644-49c8-8386-c9ffe23c872d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x ↦ x) : ∀ x, f x = x := by
  (intros; simp_all)
