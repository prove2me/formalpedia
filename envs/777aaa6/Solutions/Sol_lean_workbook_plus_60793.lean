-- Prove2me | solution 1 for lean_workbook_plus_60793
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:03.409418+00:00
-- url     : https://prove2.me/submissions/bd7cd207-3d01-4b40-8417-4910b096d67e

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2) : 2 ≥ a^2 * b + b^2 * c + c^2 * a ↔ (a + b + c)^3 ≥ 4 * (a^2 * b + b^2 * c + c^2 * a) := by
  rw [habc]
  constructor <;> intro h <;> linarith
