-- Prove2me | solution 1 for lean_workbook_plus_75180
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:06:42.235272+00:00
-- url     : https://prove2.me/submissions/7b60bca3-b4db-4299-8acf-dfc7aee99e59

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (x y z : ℝ) (hx : x ≥ 2) (hy : y ≥ 2) (hz : z ≥ 2) :
    4*(x+y+z) ≤ x*y*z+16 := by
  have hu := sub_nonneg.mpr hx
  have hv := sub_nonneg.mpr hy
  have hw := sub_nonneg.mpr hz
  have huv := mul_nonneg hu hv
  have hvw := mul_nonneg hv hw
  have hwu := mul_nonneg hw hu
  have huvw := mul_nonneg huv hw
  nlinarith only [huv, hvw, hwu, huvw]
