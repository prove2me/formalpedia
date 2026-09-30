-- Prove2me | solution 1 for lean_workbook_plus_81178
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:10.649528+00:00
-- url     : https://prove2.me/submissions/5b11903e-fd79-4c1b-aded-ce8d850b0041

import Mathlib

theorem solution (x y : ℝ) (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) :
    6 * x ^ 2 + 3 * y ^ 2 - 1 ≤ 0 ↔ 2 * x ^ 2 + y ^ 2 ≤ 1 / 3 := by
  constructor <;> intro h <;> linarith
