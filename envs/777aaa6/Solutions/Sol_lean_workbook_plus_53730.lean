-- Prove2me | solution 1 for lean_workbook_plus_53730
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:53.156779+00:00
-- url     : https://prove2.me/submissions/b1371605-9b4c-484b-9898-c8729769b3b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => -|x|) : ∀ x, f x = -|x| := by
  (intros; simp_all)
