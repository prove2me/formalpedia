-- Prove2me | solution 1 for lean_workbook_plus_57354
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:24.450165+00:00
-- url     : https://prove2.me/submissions/049f4655-5e50-470a-9c25-7e7c5b45c44b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 ≥ 0 := by
  (intros; positivity)
