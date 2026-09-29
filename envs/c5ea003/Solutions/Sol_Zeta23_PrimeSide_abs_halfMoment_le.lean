-- Prove2me | solution 1 for Zeta23.PrimeSide.abs_halfMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:15:17.77078+00:00
-- url     : https://prove2.me/submissions/4ae093d3-68dc-4ffe-9a79-59cb65e9656d

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

-- from Zeta23.PrimeSideB.PPKernel
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Kernel lemmas for [prop:PP] (§5.4)

Pure measure-theory / trigonometric-integral / H-MV-application lemmas used by
`Zeta23/PrimeSideB/PP.lean`.

* `sqIntegral_shear`: the substitution `τ = τ' + x` on the square `I×I` (§5.4).
* `intervalIntegral_cos_linear*`: `∫_α^β cos(θt + c) dt` closed forms and the bound `2/|θ|` (§5.4).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate

namespace Zeta23
namespace PrimeSide

/-! ## Elementary facts about the index range `primeRange X = Finset.Ioc 0 ⌊X⌋₊` -/

section Basics











end Basics

/-! ## The shear `(τ,τ') ↦ (x,τ') = (τ−τ',τ')` on `I × I`  (§5.4) -/

section Shear
variable {Φ : ℝ → ℝ} {T : ℝ}











end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral









variable {T : ℝ}


end CosIntegral

/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/

section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}






/-! ### The diagonal 𝒟 (§5.4) -/



/-! ### The sum-frequency terms 𝒪₂ (§5.4) -/


/-! ### The difference-frequency terms 𝒪₁, exact evaluation (§5.4) -/






end PairDecomp

/-! ## Applying H-MV on the prime-power frequencies  ([lem:MV], [eq:deltan]; §5.1, §5.4) -/

section MVapply
variable {C : ℝ}





end MVapply

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Zeta23
open PrimeSide
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem solution (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) {a b : ℝ}
    (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hg1 : ∀ x, |g x| ≤ 1) :
    |∫ x in a..b, Φ x ^ 2 * g x| ≤ ∫ x, Φ x ^ 2 := by
  rw [intervalIntegral.integral_of_le hab]
  calc |∫ x in Ioc a b, Φ x ^ 2 * g x|
      ≤ ∫ x in Ioc a b, |Φ x ^ 2 * g x| := abs_integral_le_integral_abs
    _ ≤ ∫ x in Ioc a b, Φ x ^ 2 := by
        apply setIntegral_mono_on ?_ hΦ2.integrableOn measurableSet_Ioc
        · intro x _
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          calc Φ x ^ 2 * |g x| ≤ Φ x ^ 2 * 1 := by gcongr; exact hg1 x
            _ = Φ x ^ 2 := mul_one _
        · exact (((by fun_prop : Continuous fun x => Φ x ^ 2 * g x).integrableOn_Icc
            (a := a) (b := b)).mono_set Ioc_subset_Icc_self).abs
    _ ≤ ∫ x, Φ x ^ 2 :=
        setIntegral_le_integral hΦ2 (Filter.Eventually.of_forall fun _ => sq_nonneg _)
