-- Prove2me | solution 1 for Zeta23.MuFields.mu_monotoneOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:10:16.451256+00:00
-- url     : https://prove2.me/submissions/0f320a95-22e2-462d-b05e-d4958c90b54e

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
import Theorems.Thm_Zeta23_MuFields_re_digamma_mono

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


/-- Bridge to Zeta23.mu: μ(τ) in terms of the parametrized line at a = 1/4, t = τ/2. -/
lemma mu_eq (τ : ℝ) :
    Zeta23.mu τ = (1 / (2 * Real.pi))
        * (Complex.digamma ((((1 : ℝ) / 4 : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
      - Real.log Real.pi / (2 * Real.pi) := by
  unfold Zeta23.mu
  congr 3
  push_cast
  ring




/-! ### The derivative bound μ′ ≪ 1/|τ|  (via the trigamma series) -/




end MuFields
end Zeta23
end
open Zeta23
open MuFields
open Complex Filter Topology
variable {a : ℝ}

theorem solution : MonotoneOn Zeta23.mu (Set.Ici (0 : ℝ)) := by
  intro t₁ h₁ t₂ h₂ h12
  rw [mu_eq, mu_eq]
  have hmono := re_digamma_mono (a := 1 / 4) (by norm_num) (by norm_num)
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₁] : (0 : ℝ) ≤ t₁ / 2))
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₂] : (0 : ℝ) ≤ t₂ / 2))
    (by linarith)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2π : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hmono h2π
  linarith
