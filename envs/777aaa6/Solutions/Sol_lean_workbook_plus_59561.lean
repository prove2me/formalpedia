-- Prove2me | solution 1 for lean_workbook_plus_59561
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:43.875658+00:00
-- url     : https://prove2.me/submissions/e9b375fd-8785-450d-aa2f-f62e1509da67

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d r s x y : ℝ) : x = r * a + s * c ∧ y = r * b + s * d ↔ x = r * a + s * c ∧ y = r * b + s * d := by
  norm_num
