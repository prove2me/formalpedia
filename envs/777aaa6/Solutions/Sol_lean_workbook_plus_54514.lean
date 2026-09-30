-- Prove2me | solution 1 for lean_workbook_plus_54514
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T01:13:42.354703+00:00
-- url     : https://prove2.me/submissions/4f76896e-98cb-4d3b-97f3-8ced9687f80d

import Mathlib.Analysis.Convex.SpecificFunctions.Basic

theorem solution (x : ℝ) (n : ℕ) (hn : 1 < n) (hx : -1 < x) (hx' : x ≠ 0) :
    (1 + x) ^ n > 1 + n * x := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  simpa only [Real.rpow_natCast] using
    one_add_mul_self_lt_rpow_one_add hx.le hx' hn'
