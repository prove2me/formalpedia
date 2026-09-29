-- Prove2me | Theorems.Thm_reciprocal_sum_eq_one_iff_three_three_three
-- name    : reciprocal_sum_eq_one_iff_three_three_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:54:40.546588+00:00
-- url     : https://prove2.me/theorems/5646daf2-6669-456d-93a7-1251cbb254bf
-- title:
--   Reciprocal sum eq one iff three three three
-- statement:
--   Formal statement of `reciprocal_sum_eq_one_iff_three_three_three` from the Aether Catalog (Speculative). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem reciprocal_sum_eq_one_iff_three_three_three    {x y z : ℕ} (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) :
--       ((1 : ℚ) / x + (1 : ℚ) / y + (1 : ℚ) / z = 1) ↔ (x = 3 ∧ y = 3 ∧ z = 3) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/NumberTheory/ExponentBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/NumberTheory/ExponentBounds.lean#L31

-- Thm stub generated from Speculative/NumberTheory/ExponentBounds.lean
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

theorem reciprocal_sum_eq_one_iff_three_three_three    {x y z : ℕ} (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) :
    ((1 : ℚ) / x + (1 : ℚ) / y + (1 : ℚ) / z = 1) ↔ (x = 3 ∧ y = 3 ∧ z = 3) := by sorry
