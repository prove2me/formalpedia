-- Prove2me | Definitions.Def_Probability_WignerSemicircleMoments
-- name    : Probability_WignerSemicircleMoments
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:19.295918+00:00
-- url     : https://prove2.me/theorems/7e17b86e-56e4-4fe0-ac4e-49fdc4849462
-- title:
--   Aether Catalog definitions — Probability_WignerSemicircleMoments
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerSemicircleMoments`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerSemicircleMoments.lean by skeleton subtraction
import Mathlib
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

namespace WignerSemicircle

noncomputable section

/-- `sinPowInt m = ∫_{-π/2}^{π/2} sinᵐ t dt`, the Wallis integral on the
symmetric interval. -/
def sinPowInt (m : ℕ) : ℝ := ∫ t in (-(π / 2))..(π / 2), Real.sin t ^ m

/-- The `m`-th moment of the standard Wigner semicircle law with density
`√(4 - x²) / (2π)` supported on `[-2, 2]`. -/
def semicircleMoment (m : ℕ) : ℝ :=
  (1 / (2 * π)) * ∫ x in (-2 : ℝ)..2, x ^ m * Real.sqrt (4 - x ^ 2)

/-! ### Wallis integrals on `[-π/2, π/2]` -/






/-! ### The trigonometric substitution -/




/-! ### Odd moments vanish -/


/-! ### Even moments are Catalan numbers -/




/-! ### Small cases -/




end

end WignerSemicircle


