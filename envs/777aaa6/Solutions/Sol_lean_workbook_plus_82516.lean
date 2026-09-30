-- Prove2me | solution 1 for lean_workbook_plus_82516
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:46:43.748828+00:00
-- url     : https://prove2.me/submissions/b0c060a6-0dec-4a29-9811-541afb52f127

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

private theorem term_identity (x y z k : ℝ) (hy : y ≠ 0) (hz : z ≠ 0) :
    1 / ((k*x/y)*(k*y/z+1)) = (y*z)/(k*x*(k*y+z)) := by
  have hid : (k*x/y)*(k*y/z+1) = (k*x*(k*y+z))/(y*z) := by
    field_simp [hy, hz]
  rw [hid, one_div_div]

theorem solution (x y z k a b c : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hab : a = k*x/y) (hbc : b = k*y/z) (hca : c = k*z/x) :
    1/(a*(b+1)) + 1/(b*(c+1)) + 1/(c*(a+1)) =
    (y*z)/(k*x*(k*y+z)) + (z*x)/(k*y*(k*z+x)) + (x*y)/(k*z*(k*x+y)) := by
  rw [hab, hbc, hca, term_identity x y z k hy hz,
    term_identity y z x k hz hx, term_identity z x y k hx hy]
