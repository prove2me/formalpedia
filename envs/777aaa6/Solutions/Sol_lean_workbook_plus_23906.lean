-- Prove2me | solution 1 for lean_workbook_plus_23906
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:55:54.817775+00:00
-- url     : https://prove2.me/submissions/cb547fe2-4d88-4a42-b84b-55d1dd07bbc8

import Mathlib.Analysis.Complex.Basic

theorem solution : ⌊Real.sqrt 2009⌋ = 44 := by
  rw [Int.floor_eq_iff]
  have h1 : (44 : ℝ) ≤ Real.sqrt 2009 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h2 : Real.sqrt 2009 < 45 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  constructor
  · push_cast; linarith
  · push_cast; linarith
