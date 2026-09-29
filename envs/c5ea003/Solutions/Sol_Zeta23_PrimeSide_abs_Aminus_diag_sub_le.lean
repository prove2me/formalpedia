-- Prove2me | solution 1 for Zeta23.PrimeSide.abs_Aminus_diag_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:46:13.291216+00:00
-- url     : https://prove2.me/submissions/6df6acdc-c8e7-40ed-8abd-9a8c2e9b90e9

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










lemma Ix_length {x : ℝ} :
    min (2 * T - x) (2 * T) - max (T - x) T = T - |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [abs_of_neg h, min_eq_right (by linarith), max_eq_left (by linarith)]; ring

end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral





lemma Jker_zero (c α β : ℝ) : Jker 0 c α β = (β - α) * Real.cos c := by simp [Jker]




variable {T : ℝ}


end CosIntegral

/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/

section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}




lemma not_mem_Icc_neg {x : ℝ} (hx : x ∉ Icc (-T) T) : T < |x| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rcases lt_or_ge x 0 with hx0 | hx0
    · rw [abs_of_neg hx0]; linarith
    · rw [abs_of_nonneg hx0]; linarith
  · exact lt_of_lt_of_le h (le_abs_self x)


/-! ### The diagonal 𝒟 (§5.4) -/

lemma JmK_diag (T y x : ℝ) : JmK T y y x = (T - |x|) * Real.cos (x * y) := by
  unfold JmK; rw [sub_self, Jker_zero, Ix_length]


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

theorem solution (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) (y : ℝ) :
    |Aminus Φ T y y - T * ∫ x, Φ x ^ 2 * Real.cos (x * y)| ≤ ∫ x, Φ x ^ 2 * |x| := by
  unfold Aminus
  simp_rw [JmK_diag]
  set f : ℝ → ℝ := fun x => Φ x ^ 2 * ((T - |x|) * Real.cos (x * y)) with hf
  have hA : Integrable ((Icc (-T) T).indicator f) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((by fun_prop : Continuous f).integrableOn_Icc)
  have hB : Integrable fun x => T * (Φ x ^ 2 * Real.cos (x * y)) := by
    refine (hΦ2.mul_bdd (c := 1) (by fun_prop) ?_).const_mul T
    exact Filter.Eventually.of_forall fun x => by
      simpa using Real.abs_cos_le_one (x * y)
  rw [← integral_indicator measurableSet_Icc, ← integral_const_mul, ← integral_sub hA hB]
  calc |∫ x, ((Icc (-T) T).indicator f x - T * (Φ x ^ 2 * Real.cos (x * y)))|
      ≤ ∫ x, |(Icc (-T) T).indicator f x - T * (Φ x ^ 2 * Real.cos (x * y))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, Φ x ^ 2 * |x| := by
        apply integral_mono (hA.sub hB).abs hΦabs
        intro x
        change |(Icc (-T) T).indicator f x - T * (Φ x ^ 2 * Real.cos (x * y))| ≤ Φ x ^ 2 * |x|
        have hc := Real.abs_cos_le_one (x * y)
        have hΦ0 : 0 ≤ Φ x ^ 2 := sq_nonneg _
        by_cases hx : x ∈ Icc (-T) T
        · rw [Set.indicator_of_mem hx, hf]
          simp only
          have : |x| ≤ T := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
          calc |Φ x ^ 2 * ((T - |x|) * Real.cos (x * y)) - T * (Φ x ^ 2 * Real.cos (x * y))|
              = Φ x ^ 2 * |x| * |Real.cos (x * y)| := by
                rw [show Φ x ^ 2 * ((T - |x|) * Real.cos (x * y)) - T * (Φ x ^ 2 * Real.cos (x * y))
                    = -(Φ x ^ 2 * |x| * Real.cos (x * y)) by ring, abs_neg, abs_mul, abs_mul,
                  abs_of_nonneg hΦ0, abs_abs]
            _ ≤ Φ x ^ 2 * |x| * 1 := by gcongr
            _ = Φ x ^ 2 * |x| := mul_one _
        · rw [Set.indicator_of_notMem hx, zero_sub, abs_neg, abs_mul, abs_mul, abs_of_nonneg hT,
            abs_of_nonneg hΦ0]
          have : T < |x| := not_mem_Icc_neg hx
          calc T * (Φ x ^ 2 * |Real.cos (x * y)|) ≤ |x| * (Φ x ^ 2 * 1) := by gcongr
            _ = Φ x ^ 2 * |x| := by ring
