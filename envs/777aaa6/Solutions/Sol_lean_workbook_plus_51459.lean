-- Prove2me | solution 1 for lean_workbook_plus_51459
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:18:36.726093+00:00
-- url     : https://prove2.me/submissions/82de8e62-36ab-4c59-ab17-500aa4ef0e67

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (2 * a - b - c) ^ 2 ≥ 0 := by
  (intros; positivity)
