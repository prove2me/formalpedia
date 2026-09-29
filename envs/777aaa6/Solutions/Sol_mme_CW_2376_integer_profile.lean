-- Prove2me | solution 1 for mme_CW_2376_integer_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:54:58.621449+00:00
-- url     : https://prove2.me/submissions/9d4f550b-317a-4d32-a8d5-8d4cfbd0f57c

import Mathlib.Tactic

/-!
# Exact integer profile for the CW 2.376 certificate

Using denominator `3,000,000`, the paper's four rational frequencies have
integer numerators `699`, `37,518`, `307,638`, and `616,627`.  Equation (13)
then gives the five displayed marginal numerators.
-/

theorem solution (m : ℕ) :
    3 * (699 * m) + 6 * (37518 * m) +
        3 * (307638 * m) + 3 * (616627 * m) = 3000000 * m ∧
    2 * (699 * m) + 2 * (37518 * m) + 307638 * m = 384072 * m ∧
    2 * (37518 * m) + 2 * (616627 * m) = 1308290 * m ∧
    2 * (307638 * m) + 616627 * m = 1231903 * m ∧
    2 * (37518 * m) = 75036 * m ∧
    699 * m = 699 * m ∧
    384072 * m + 1308290 * m + 1231903 * m +
        75036 * m + 699 * m = 3000000 * m := by
  omega

