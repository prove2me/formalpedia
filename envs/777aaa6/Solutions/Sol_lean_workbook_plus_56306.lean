-- Prove2me | solution 1 for lean_workbook_plus_56306
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:42.582298+00:00
-- url     : https://prove2.me/submissions/78f5a983-da0b-4272-b8c5-162b4bc7287d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b) * (b + c) * (c + a) / a / b / c - 24 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 = (a + b - 3 * c) ^ 2 * (a - b) ^ 2 / (a * b * (a + b + c) ^ 2) + (b + c - 3 * a) ^ 2 * (b - c) ^ 2 / (b * c * (a + b + c) ^ 2) + (c + a - 3 * b) ^ 2 * (c - a) ^ 2 / (c * a * (a + b + c) ^ 2) := by
  (intros; field_simp; ring)
