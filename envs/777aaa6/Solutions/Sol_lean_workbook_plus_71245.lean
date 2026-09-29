-- Prove2me | solution 1 for lean_workbook_plus_71245
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:13.261845+00:00
-- url     : https://prove2.me/submissions/bc37c65a-a6c9-4911-8afe-c8787ba4b06c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a q x y z w : ℝ) : (x = -46 - a - 6*q + 3*a*q ∧ y = -5*a + 6*q - 2*a*q ∧ z = 46 - 17*a ∧ w = q - 23 → x/w = (-46 - a - 6*q + 3*a*q)/(q - 23) ∧ y/w = (-5*a + 6*q - 2*a*q)/(q - 23) ∧ z/w = (46 - 17*a)/(q - 23)) := by
  (intros; simp_all)
