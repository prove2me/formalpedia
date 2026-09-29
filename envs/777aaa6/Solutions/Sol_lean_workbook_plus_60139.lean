-- Prove2me | solution 1 for lean_workbook_plus_60139
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:08.341927+00:00
-- url     : https://prove2.me/submissions/8a123315-dd63-4322-b2c2-2a06c04520eb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 8 * (a * b * c) / (b + c) / (c + a) / (a + b) + 4 * (b * a) / (b + c) / (c + a) + 4 * (a * c) / (a + b) / (b + c) + 4 * (b * c) / (c + a) / (a + b) = 4 := by
  (intros; field_simp; ring)
