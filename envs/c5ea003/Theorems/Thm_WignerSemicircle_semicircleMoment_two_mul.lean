-- Prove2me | Theorems.Thm_WignerSemicircle_semicircleMoment_two_mul
-- name    : WignerSemicircle.semicircleMoment_two_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:02:07.575154+00:00
-- url     : https://prove2.me/theorems/a20bdf90-7ba1-4988-a43b-a7af9e64e018
-- title:
--   Even moments of the semicircle law are Catalan numbers.
-- statement:
--   **Even moments of the semicircle law are Catalan numbers.**
--
--   ```lean
--   theorem WignerSemicircle.semicircleMoment_two_mul(k : ℕ) : semicircleMoment (2 * k) = catalan k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSemicircleMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSemicircleMoments.lean#L150

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




/-! ### Odd moments vanish -/


/-! ### Even moments are Catalan numbers -/

theorem WignerSemicircle.semicircleMoment_two_mul(k : ℕ) : semicircleMoment (2 * k) = catalan k := by sorry
