-- Prove2me | Theorems.Thm_WignerSemicircle_semicircleMoment_zero
-- name    : WignerSemicircle.semicircleMoment_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:23:38.229137+00:00
-- url     : https://prove2.me/theorems/a9858bb2-053e-4d90-8b52-d0c5d0f2b802
-- title:
--   SemicircleMoment zero
-- statement:
--   Formal statement of `WignerSemicircle.semicircleMoment_zero` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem WignerSemicircle.semicircleMoment_zero: semicircleMoment 0 = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSemicircleMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSemicircleMoments.lean#L179

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




/-! ### Small cases -/

theorem WignerSemicircle.semicircleMoment_zero: semicircleMoment 0 = 1 := by sorry
