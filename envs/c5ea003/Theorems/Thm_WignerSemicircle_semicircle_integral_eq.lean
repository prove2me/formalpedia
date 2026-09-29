-- Prove2me | Theorems.Thm_WignerSemicircle_semicircle_integral_eq
-- name    : WignerSemicircle.semicircle_integral_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:01:58.81744+00:00
-- url     : https://prove2.me/theorems/8c9b7beb-64fb-43f2-9ab4-322ef8169455
-- title:
--   Substituting `x = 2 sin t` turns the semicircle integral into a Wallis-type
-- statement:
--   Substituting `x = 2 sin t` turns the semicircle integral into a Wallis-type
--   trigonometric integral.
--
--   ```lean
--   theorem WignerSemicircle.semicircle_integral_eq(m : ℕ) :
--       (∫ x in (-2 : ℝ)..2, x ^ m * Real.sqrt (4 - x ^ 2)) =
--         2 ^ (m + 2) * ∫ t in (-(π / 2))..(π / 2), Real.sin t ^ m * Real.cos t ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSemicircleMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSemicircleMoments.lean#L68

-- Thm stub generated from Probability/WignerSemicircleMoments.lean
import Mathlib
import Definitions.Def_Probability_WignerSemicircleMoments
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Moments of the Wigner semicircle law are the Catalan numbers

This file establishes the analytic half of the moment method for the Wigner
semicircle law: the `m`-th moment of the standard semicircle distribution
(density `√(4 - x²)/(2π)` on `[-2, 2]`) vanishes for odd `m` and equals the
Catalan number `Cₖ` for `m = 2k`.

The proof runs through the trigonometric substitution `x = 2 sin t`, the
Mathlib reduction formula `integral_sin_pow`, and the Catalan recursion
`(k+2) Cₖ₊₁ = 2(2k+1) Cₖ` extracted from the central binomial coefficients.
-/

open Real intervalIntegral MeasureTheory
open scoped Nat

open WignerSemicircle

noncomputable section



/-! ### Wallis integrals on `[-π/2, π/2]` -/






/-! ### The trigonometric substitution -/

theorem WignerSemicircle.semicircle_integral_eq(m : ℕ) :
    (∫ x in (-2 : ℝ)..2, x ^ m * Real.sqrt (4 - x ^ 2)) =
      2 ^ (m + 2) * ∫ t in (-(π / 2))..(π / 2), Real.sin t ^ m * Real.cos t ^ 2 := by sorry
