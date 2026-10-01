-- Prove2me | Theorems.Thm_burau_cf_sub_bounds_ge_one
-- name    : burau_cf_sub_bounds_ge_one
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T21:41:37.722982+00:00
-- url     : https://prove2.me/theorems/da6ee817-899e-4a9d-abba-f0739fc128f6
-- title:
--   Size bounds when the leading quotient of a continued fraction is at least one
-- statement:
--   **Size bounds for a rational whose leading continued-fraction quotient is at least $1$.**
--   For integers $a>0$ and $b$ with $b/a\ge 1$ (integer division), one has
--   $$ 0\le b-a < b . $$
--   This is the elementary bound that lets the negative-divisor Euclidean identities be phrased uniformly
--   and is used, with the quotient and remainder formulas for a negated dividend, to obtain the first step
--   of the negative-reciprocal rule of continued fractions.
-- source:
--   Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Mathlib

set_option autoImplicit false

theorem burau_cf_sub_bounds_ge_one (a b : ℤ) (ha : 0 < a) (h : 1 ≤ b / a) :
    0 ≤ b - a ∧ b - a < b := by sorry
