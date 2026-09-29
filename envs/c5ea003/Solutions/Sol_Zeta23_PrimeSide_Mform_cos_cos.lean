-- Prove2me | solution 1 for Zeta23.PrimeSide.Mform_cos_cos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:21:47.314971+00:00
-- url     : https://prove2.me/submissions/1f886040-b21e-4de0-813b-870c11b9843b

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
import Theorems.Thm_Zeta23_PrimeSide_inner_cos_cos
import Theorems.Thm_Zeta23_PrimeSide_sqIntegral_shear

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








/-- For `T ≥ 0` the window `I∩(I−x)` is empty unless `|x| ≤ T`; so the `x`-integral may be
restricted to `[−T, T]` (§5.4 "which is empty for |x| ≥ T"). -/
lemma Ix_eq_empty (_hT : 0 ≤ T) {x : ℝ} (hx : T < |x|) : Ix T x = ∅ := by
  unfold Ix
  apply Set.Icc_eq_empty
  intro hle
  have h1 : T - x ≤ 2 * T := le_trans (le_max_left _ _) (hle.trans (min_le_right _ _))
  have h2 : T ≤ 2 * T - x := le_trans (le_max_right _ _) (hle.trans (min_le_left _ _))
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx; linarith
  · rw [abs_of_neg h] at hx; linarith



end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral








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
lemma continuous_JpK (T y y' : ℝ) : Continuous (JpK T y y') := by
  unfold JpK; exact continuous_Jker_offset _ _ _


lemma not_mem_Icc_neg {x : ℝ} (hx : x ∉ Icc (-T) T) : T < |x| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rcases lt_or_ge x 0 with hx0 | hx0
    · rw [abs_of_neg hx0]; linarith
    · rw [abs_of_nonneg hx0]; linarith
  · exact lt_of_lt_of_le h (le_abs_self x)


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

theorem solution (hT : 0 ≤ T) (hΦ : Continuous Φ) (y y' : ℝ) :
    Mform Φ T (fun τ => Real.cos (τ * y)) (fun τ => Real.cos (τ * y'))
      = (Aminus Φ T y y' + Aplus Φ T y y') / 2 := by
  unfold Mform Aminus Aplus
  have h1 : (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * y) * Real.cos (q.2 * y'))
      = fun q => Φ (q.1 - q.2) ^ 2 *
          (fun q : ℝ × ℝ => Real.cos (q.1 * y) * Real.cos (q.2 * y')) q := by
    funext q; ring
  rw [h1, sqIntegral_shear hΦ (by fun_prop)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-T) T) ?zero]
  case zero =>
    intro x hx
    rw [Ix_eq_empty hT (not_mem_Icc_neg hx)]; simp
  have h2 : ∀ x ∈ Icc (-T) T,
      Φ x ^ 2 * ∫ τ' in Ix T x, Real.cos ((x + τ') * y) * Real.cos (τ' * y')
        = (Φ x ^ 2 * JmK T y y' x + Φ x ^ 2 * JpK T y y' x) / 2 := by
    intro x hx
    rw [inner_cos_cos hT (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)]
    unfold JmK JpK; ring
  rw [setIntegral_congr_fun measurableSet_Icc h2, integral_div, integral_add]
  · exact ((hΦ.pow 2).mul (continuous_JmK T y y')).integrableOn_Icc
  · exact ((hΦ.pow 2).mul (continuous_JpK T y y')).integrableOn_Icc
