-- Prove2me | solution 1 for lean_workbook_plus_33813
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:39:13.282753+00:00
-- url     : https://prove2.me/submissions/146d0d6a-2b16-4585-abf8-1d84f0a96c68

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℤ) (hx : 1 ≤ x ∧ x ≤ 15) : 1 ≤ x ∧ x ≤ 15 := by
  (intros; simp_all)
