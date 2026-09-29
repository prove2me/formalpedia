-- Prove2me | solution 1 for Zeta23.MuFields.mu_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:08:05.110068+00:00
-- url     : https://prove2.me/submissions/c92681f7-e3f0-46c9-9d47-31f3186b6730

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series
import Theorems.Thm_Zeta23_MuFields_mu_monotoneOn
import Theorems.Thm_Zeta23_mu_even

-- from Zeta23.GammaFacts.Mu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Mu.lean — the remaining H-Γ fields from the digamma series.  Canonical text: the paper [eq:mufacts]:
"μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1, μ(τ) = (1/2π)log(|τ|/2π)
+ O(τ⁻²), μ′(τ) ≪ |τ|⁻¹ (|τ| ≥ 1)" plus the [eq:muints] integrals.
The ψ-toolkit is developed at a parametrized abscissa
a ∈ (0,1) (covers ζ's a = 1/4 and, composed with the recurrence, Theorem E's
a = 1/4 + κ/2).  Foundation: Zeta23.DigammaSeries.
-/

noncomputable section

namespace Zeta23
namespace MuFields

open Complex Filter Topology

variable {a : ℝ}






/-! ### Monotonicity on the vertical line, and the μ order facts -/






/-! ### The derivative bound μ′ ≪ 1/|τ|  (via the trigamma series) -/




end MuFields
end Zeta23
end
open Zeta23
open MuFields
open Complex Filter Topology
variable {a : ℝ}

theorem solution (τ : ℝ) : Zeta23.mu 0 ≤ Zeta23.mu τ := by
  have heven := Zeta23.mu_even
  rcases le_total 0 τ with h | h
  · exact mu_monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
  · have h1 : Zeta23.mu τ = Zeta23.mu (-τ) := (heven τ).symm
    rw [h1]
    exact mu_monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith)) (by linarith)
