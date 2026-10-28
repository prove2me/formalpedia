-- Prove2me | Theorems.Thm_gpy_integral_one_sub_pow
-- name    : gpy_integral_one_sub_pow
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T17:10:04.772547+00:00
-- url     : https://prove2.me/theorems/13160f5e-7a51-47f9-bd3c-cbe72b811c28
-- title:
--   Integral of (1-x)^m over [0,1]
-- statement:
--   For every natural number m, the integral over [0,1] of (1 - x)^m equals 1/(m + 1). This is the degree integral in the Selberg singular-sum evaluation.
-- source:
--   GPY monomial-sum evaluation: the degree integral in closed form, by reflection substitution and integral_pow

import Mathlib
open Classical

theorem gpy_integral_one_sub_pow (m : ℕ) :
    ∫ x in (0 : ℝ)..1, (1 - x) ^ m = 1 / ((m : ℝ) + 1) := by sorry
