-- Prove2me | solution 1 for mme_CW_square_profile_marginal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:50:15.811447+00:00
-- url     : https://prove2.me/submissions/050e8f00-0b2c-4532-a5fd-d20e7b58cc5d

import Mathlib.Tactic

/-!
# Integer form of the CW equation-(13) marginals

For an integer joint profile with orbit multiplicities `A,B,C,D`, the five
mode marginals are `2A+2B+C`, `2B+2D`, `2C+D`, `2B`, and `A`.  Their sum is
the profile length whenever `3A+6B+3C+3D=N`.
-/

theorem solution
    (A B C D N : ℕ)
    (hnorm : 3 * A + 6 * B + 3 * C + 3 * D = N) :
    (2 * A + 2 * B + C) + (2 * B + 2 * D) +
        (2 * C + D) + 2 * B + A = N := by
  omega
