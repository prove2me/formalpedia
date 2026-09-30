-- Prove2me | solution 1 for lean_workbook_plus_78856
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:50:57.445732+00:00
-- url     : https://prove2.me/submissions/e664e3bf-2f4e-4244-827f-41fa65590cd2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution {a b c : ℝ} (hx : a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    -a^3 + a^2 * b + a^2 * c + a * b^2 - 2 * a * b * c + a * c^2
      - b^3 + b^2 * c + b * c^2 - c^3 ≥ 0 := by
  have hp := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hbc.le))
    (sub_nonneg.mpr hca.le)
  nlinarith only [hp]
