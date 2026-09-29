-- Prove2me | solution 1 for lean_workbook_plus_70315
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:33.27254+00:00
-- url     : https://prove2.me/submissions/861b09dd-796b-466f-ab38-7d9ddc753c85

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x + 1) ^ 2 + (y + 1) ^ 2 + (x - y) ^ 2 ≥ 0 := by
  (intros; positivity)
