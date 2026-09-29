-- Prove2me | solution 1 for reciprocal_sum_eq_one_iff_three_three_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:26:21.537587+00:00
-- url     : https://prove2.me/submissions/a7eddee2-8b8e-439e-ba4c-5adb3a2337c4

-- Sol generated from Speculative/NumberTheory/ExponentBounds.lean
import Mathlib
/-
Copyright (c) 2025. All rights reserved.

# Exponent Reciprocal Bounds and Fermat–Catalan Connection

This file proves that for exponents `x, y, z > 2`:
1. `1/x + 1/y + 1/z ≤ 1` (the Beal exponent regime sits at or below the
   Fermat–Catalan threshold)
2. Equality holds iff `x = y = z = 3` (the cubic boundary case)

These results formally position Beal inside the landscape of generalized
Fermat equations and show why abc/Fermat–Catalan technology is naturally adjacent.
-/

/-! ## Reciprocal sum bound -/

/-
For exponents `x, y, z > 2`, the sum of reciprocals is at most 1.
This places Beal solutions in the "hyperbolic" or "boundary" regime
of the Fermat–Catalan classification.
-/

/-
The reciprocal sum equals 1 if and only if all exponents are exactly 3.
This identifies `(3,3,3)` as the unique boundary case.
-/

/-
For exponents `x, y, z > 2` not all equal to 3, the reciprocal sum is strictly less than 1.
This is the regime where Fermat–Catalan predicts only finitely many primitive solutions.
-/

theorem solution    {x y z : ℕ} (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) :
    ((1 : ℚ) / x + (1 : ℚ) / y + (1 : ℚ) / z = 1) ↔ (x = 3 ∧ y = 3 ∧ z = 3) := by
  constructor <;> intro H;
  · -- Assume that $x$, $y$, and $z$ are all greater than 2 and satisfy the equation. We'll derive a contradiction if any of them is greater than 3.
    by_cases hx3 : x > 3
    by_cases hy3 : y > 3
    by_cases hz3 : z > 3;
    · field_simp at H;
      norm_cast at H; nlinarith only [ mul_pos ( by linarith : 0 < y ) ( by linarith : 0 < z ), mul_pos ( by linarith : 0 < x ) ( by linarith : 0 < z ), mul_pos ( by linarith : 0 < x ) ( by linarith : 0 < y ), H, hx3, hy3, hz3 ] ;
    · interval_cases z ; norm_num at *;
      field_simp at H;
      norm_cast at H; nlinarith;
    · interval_cases y ; norm_num at *;
      field_simp at H;
      norm_cast at H; nlinarith [ show z = 2 by nlinarith ] ;
    · interval_cases x ; norm_num at *;
      field_simp at H;
      norm_cast at H; rcases y with ( _ | _ | _ | _ | y ) <;> rcases z with ( _ | _ | _ | _ | z ) <;> norm_num at * <;> nlinarith;
  · norm_num [ H ]
