-- Prove2me | solution 1 for lean_workbook_plus_19095
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:03:52.994779+00:00
-- url     : https://prove2.me/submissions/0524b348-9202-4661-abbf-ad95fc4e2f9d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : 2 * (x * y) / (x + y) = 2 / (1 / x + 1 / y) := by
  (intros; field_simp; ring)
