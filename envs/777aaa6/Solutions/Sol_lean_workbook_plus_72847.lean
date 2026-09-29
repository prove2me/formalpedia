-- Prove2me | solution 1 for lean_workbook_plus_72847
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:21:19.196865+00:00
-- url     : https://prove2.me/submissions/03949da0-ac36-447a-a1d6-9e6e29ae3986

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c d e : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) : (a - b) ^ 2 + (a - c) ^ 2 + (a - d) ^ 2 + (a - e) ^ 2 + (b - c) ^ 2 + (b - d) ^ 2 + (b - e) ^ 2 + (c - d) ^ 2 + (c - e) ^ 2 + (d - e) ^ 2 ≥ 0 := by
  (intros; positivity)
