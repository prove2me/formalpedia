-- Prove2me | solution 1 for lean_workbook_plus_43926
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:45.886396+00:00
-- url     : https://prove2.me/submissions/d07947cc-a42e-441e-b823-41983362936d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hab : a + b + c = 1) : a^2 + b^2 + c^2 + Real.sqrt (12 * a * b * c) ≤ 1 := by
  (intros; linarith)
