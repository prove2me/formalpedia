-- Prove2me | solution 1 for Zeta23.PrimeSide.sub_mul_Aminus_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:13:40.76065+00:00
-- url     : https://prove2.me/submissions/009cd118-699c-46a3-af1f-fedc08a47850

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






lemma Jker_of_ne {θ : ℝ} (hθ : θ ≠ 0) (c α β : ℝ) :
    Jker θ c α β = (Real.sin (θ * β + c) - Real.sin (θ * α + c)) / θ := by simp [Jker, hθ]


/-- `J` as a function of the offset `x` (through `c = xy`, `α = max(T−x,T)`, `β = min(2T−x,2T)`)
is continuous. -/
lemma continuous_Jker_offset (θ y T : ℝ) :
    Continuous fun x : ℝ => Jker θ (x * y) (max (T - x) T) (min (2 * T - x) (2 * T)) := by
  by_cases hθ : θ = 0
  · simp only [Jker, hθ, if_true]; fun_prop
  · simp only [Jker, hθ, if_false]; fun_prop

variable {T : ℝ}


end CosIntegral

/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/

section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}


lemma continuous_JmK (T y y' : ℝ) : Continuous (JmK T y y') := by
  unfold JmK; exact continuous_Jker_offset _ _ _




/-! ### The diagonal 𝒟 (§5.4) -/



/-! ### The sum-frequency terms 𝒪₂ (§5.4) -/


/-! ### The difference-frequency terms 𝒪₁, exact evaluation (§5.4) -/


/-- linearity step: ∫_a^b Φ²[sin(c₁+xy) − sin(c₂+xy')] in terms of the cos/sin moments. -/
lemma integral_sq_mul_sin_sub_sin (hΦ : Continuous Φ) (a b c₁ c₂ y y' : ℝ) :
    ∫ x in a..b, Φ x ^ 2 * (Real.sin (c₁ + x * y) - Real.sin (c₂ + x * y'))
      = (Real.sin c₁ * ∫ x in a..b, Φ x ^ 2 * Real.cos (x * y))
        + (Real.cos c₁ * ∫ x in a..b, Φ x ^ 2 * Real.sin (x * y))
        - ((Real.sin c₂ * ∫ x in a..b, Φ x ^ 2 * Real.cos (x * y'))
          + (Real.cos c₂ * ∫ x in a..b, Φ x ^ 2 * Real.sin (x * y'))) := by
  have e : ∀ x, Φ x ^ 2 * (Real.sin (c₁ + x * y) - Real.sin (c₂ + x * y'))
      = (Real.sin c₁ * (Φ x ^ 2 * Real.cos (x * y)) + Real.cos c₁ * (Φ x ^ 2 * Real.sin (x * y)))
        - (Real.sin c₂ * (Φ x ^ 2 * Real.cos (x * y'))
            + Real.cos c₂ * (Φ x ^ 2 * Real.sin (x * y'))) := by
    intro x; rw [Real.sin_add, Real.sin_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  all_goals apply Continuous.intervalIntegrable; fun_prop




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

theorem solution (hT : 0 ≤ T) (hΦ : Continuous Φ) {y y' : ℝ} (hθ : y - y' ≠ 0) :
    (y - y') * Aminus Φ T y y'
      = (Real.sin ((y - y') * (2 * T)) * Cm Φ T y + Real.cos ((y - y') * (2 * T)) * Sm Φ T y
          - (Real.sin ((y - y') * T) * Cm Φ T y' + Real.cos ((y - y') * T) * Sm Φ T y'))
        + (Real.sin ((y - y') * (2 * T)) * Cp Φ T y' + Real.cos ((y - y') * (2 * T)) * Sp Φ T y'
          - (Real.sin ((y - y') * T) * Cp Φ T y + Real.cos ((y - y') * T) * Sp Φ T y)) := by
  unfold Aminus Cm Sm Cp Sp
  have hcont : Continuous fun x => Φ x ^ 2 * ((y - y') * JmK T y y' x) := by
    have := continuous_JmK T y y'; fun_prop
  rw [← integral_const_mul]
  have e1 : ∀ x, (y - y') * (Φ x ^ 2 * JmK T y y' x) = Φ x ^ 2 * ((y - y') * JmK T y y' x) := by
    intro x; ring
  simp_rw [e1]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  -- left half: x ∈ [−T, 0], window [T−x, 2T]
  have hL : ∫ x in (-T)..0, Φ x ^ 2 * ((y - y') * JmK T y y' x)
      = ∫ x in (-T)..0, Φ x ^ 2 * (Real.sin ((y - y') * (2 * T) + x * y)
          - Real.sin ((y - y') * T + x * y')) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -T ≤ 0)] at hx
    simp only
    congr 1
    unfold JmK
    rw [max_eq_left (by linarith [hx.2]), min_eq_right (by linarith [hx.2]), Jker_of_ne hθ,
      mul_div_cancel₀ _ hθ]
    congr 1
    rw [show (y - y') * (T - x) + x * y = (y - y') * T + x * y' by ring]
  -- right half: x ∈ [0, T], window [T, 2T−x]
  have hR : ∫ x in (0:ℝ)..T, Φ x ^ 2 * ((y - y') * JmK T y y' x)
      = ∫ x in (0:ℝ)..T, Φ x ^ 2 * (Real.sin ((y - y') * (2 * T) + x * y')
          - Real.sin ((y - y') * T + x * y)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    simp only
    congr 1
    unfold JmK
    rw [max_eq_right (by linarith [hx.1]), min_eq_left (by linarith [hx.1]), Jker_of_ne hθ,
      mul_div_cancel₀ _ hθ]
    congr 1
    rw [show (y - y') * (2 * T - x) + x * y = (y - y') * (2 * T) + x * y' by ring]
  rw [hL, hR, integral_sq_mul_sin_sub_sin hΦ, integral_sq_mul_sin_sub_sin hΦ]
