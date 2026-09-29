-- Prove2me | solution 1 for lean_workbook_plus_60301
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:52.491975+00:00
-- url     : https://prove2.me/submissions/a83e2614-58c9-4c62-9f99-85cbf45fde86

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 - (a * (a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2) + b * (b ^ 2 + 3 * c ^ 2 + 3 * a ^ 2) + c * (c ^ 2 + 3 * a ^ 2 + 3 * b ^ 2)) ≥ 0 ↔ 6 * a * b * c ≥ 0 := by
  (intros; ring)
