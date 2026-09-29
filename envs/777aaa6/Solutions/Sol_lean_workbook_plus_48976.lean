-- Prove2me | solution 1 for lean_workbook_plus_48976
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:17.33591+00:00
-- url     : https://prove2.me/submissions/c3da1206-39e7-4d93-a20d-89249e5ecc6c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f g s : ℝ → ℝ) (r : ℝ) (s_def : s = f + g) : s r = f r + g r := by
  (intros; simp_all)
