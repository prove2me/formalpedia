-- Prove2me | solution 1 for lean_workbook_plus_64935
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:58.003508+00:00
-- url     : https://prove2.me/submissions/fe20e1c0-dfbf-40ed-88bf-7f02f7f971d8

import Mathlib.Analysis.Complex.Basic

theorem solution : ∑' i : ℕ, (1/2)^i = 1 := by
  rw [tsum_eq_single 0]
  · norm_num
  · intro b hb
    norm_num
    exact hb
