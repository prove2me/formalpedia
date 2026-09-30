-- Prove2me | solution 1 for lean_workbook_plus_74493
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:35:59.348626+00:00
-- url     : https://prove2.me/submissions/ee68bb8e-ab54-452b-8bdc-91cebdc04c64

import Mathlib

set_option autoImplicit false

theorem solution (t : ℝ) : 6 * t ^ 2 - 77 * t + 147 ≤ 0 ↔ 7 / 3 ≤ t ∧ t ≤ 10.5 := by
  constructor
  · intro h
    constructor
    · nlinarith [sq_nonneg (t - 7 / 3)]
    · nlinarith [sq_nonneg (t - 21 / 2)]
  · rintro ⟨hlo, hhi⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
