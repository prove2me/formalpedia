-- Prove2me | Theorems.Thm_mme_positive_binary_ternary_entropy_optimizer
-- name    : mme_positive_binary_ternary_entropy_optimizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:52:57.021107+00:00
-- url     : https://prove2.me/theorems/c9d7a731-543b-4fea-97ed-67b36352b141
-- title:
--   Exact positive binary and ternary entropy optimizers
-- statement:
--   For positive real weights x, y, z, the binary and ternary entropy products evaluated at the normalized weights x/(x+y), y/(x+y), and x/(x+y+z), y/(x+y+z), z/(x+y+z) equal their total mass. This is the exact algebraic optimizer identity repeatedly used in Davie--Stothers Lemma 5.1 and later laser-method analyses.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.4 and Lemma 5.1, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Real

set_option autoImplicit false

theorem mme_positive_binary_ternary_entropy_optimizer
    (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((x / (x / (x + y))) ^ (x / (x + y)) *
        (y / (y / (x + y))) ^ (y / (x + y)) = x + y) ∧
      ((x / (x / (x + y + z))) ^ (x / (x + y + z)) *
          (y / (y / (x + y + z))) ^ (y / (x + y + z)) *
          (z / (z / (x + y + z))) ^ (z / (x + y + z)) =
        x + y + z) := by
  sorry
