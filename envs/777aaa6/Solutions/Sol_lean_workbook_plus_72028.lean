-- Prove2me | solution 1 for lean_workbook_plus_72028
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:57:45.784588+00:00
-- url     : https://prove2.me/submissions/65a773f5-596d-4325-bc70-a609f7a74558

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (hab : a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1)
    (h : a*b+b*c+c*a = 4) : 5*a+4*b+c ≤ 25/2 := by
  have hp := mul_nonneg (sub_nonneg.mpr hab.1) (sub_nonneg.mpr hab.2.1)
  have hq := mul_nonneg (sub_nonneg.mpr hab.2.1) (sub_nonneg.mpr hab.2.2)
  have hr := mul_nonneg (sub_nonneg.mpr hab.2.2) (sub_nonneg.mpr hab.1)
  nlinarith only [hp, hq, hr, h, hab.2.1, hab.2.2]
