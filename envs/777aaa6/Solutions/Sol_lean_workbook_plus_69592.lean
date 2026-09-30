-- Prove2me | solution 1 for lean_workbook_plus_69592
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:03:13.510751+00:00
-- url     : https://prove2.me/submissions/2b065bfb-4a3e-45f0-9689-0f7cbe5d5d66

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c d : ℝ) (h1 : a ≥ c ∧ c ≥ 0) (h2 : b ≥ d ∧ d ≥ 0) :
    (a+b+c+d)^2 ≥ 8*(a*d+b*c) := by
  have hp := mul_nonneg (sub_nonneg.mpr h1.1) (sub_nonneg.mpr h2.1)
  nlinarith only [hp, sq_nonneg (a+c-b-d)]
