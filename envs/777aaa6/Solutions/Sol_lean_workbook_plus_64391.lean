-- Prove2me | solution 1 for lean_workbook_plus_64391
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:38.056923+00:00
-- url     : https://prove2.me/submissions/6cea364e-bf47-40e0-bc39-3817677ac5d9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : ∃ l, ∑' n : ℕ, (a^(1/n) - (b^(1/n) + c^(1/n)) / 2) = l := by
  norm_num
