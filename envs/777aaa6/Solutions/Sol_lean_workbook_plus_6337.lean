-- Prove2me | solution 1 for lean_workbook_plus_6337
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:29.4525+00:00
-- url     : https://prove2.me/submissions/3bf129cc-8e30-48a1-b6ac-10d05393453d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 0 ≤ (1 / 4) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) * ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a)) := by
  (intros; positivity)
