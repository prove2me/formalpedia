-- Prove2me | solution 1 for Zeta23.PrimeSide.MV_size_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:26:51.329642+00:00
-- url     : https://prove2.me/submissions/478942dd-21ee-4e72-8bea-e0f688836357

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

lemma one_le_of_mem_primeRange {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) : 1 ≤ n :=
  (Finset.mem_Ioc.mp hn).1






/-- a_n² = Λ(n)²/n (§5.4). -/
lemma acoef_sq (n : ℕ) : acoef n ^ 2 = (Λ n : ℝ) ^ 2 / n := by
  unfold acoef; rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- 2n·a_n² = 2Λ(n)² — the MV weight with δ_n = 1/(2n) [eq:deltan]. -/
lemma acoef_sq_mul_two_mul {n : ℕ} (hn : 1 ≤ n) : acoef n ^ 2 * (2 * n) = 2 * (Λ n : ℝ) ^ 2 := by
  rw [acoef_sq]
  have : (0:ℝ) < n := by exact_mod_cast hn
  field_simp



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
variable {C : ℝ}

theorem solution (hC : 0 ≤ C) (X : ℝ) {w : ℕ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ n ∈ primeRange X, |w n| ≤ W) :
    C * Real.sqrt (∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 ∧
    C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := by
  set Λ2 := ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 with hΛ2
  have hΛ2nn : 0 ≤ Λ2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have h1 : ∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n) = 2 * Λ2 := by
    rw [hΛ2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n hn => acoef_sq_mul_two_mul (one_le_of_mem_primeRange hn)
  have h2 : ∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n) ≤ W ^ 2 * (2 * Λ2) := by
    rw [hΛ2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [mul_pow, mul_comm (acoef n ^ 2), mul_assoc, acoef_sq_mul_two_mul (one_le_of_mem_primeRange hn)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (sq_abs (w n)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hw n hn) 2
  have hs1 : Real.sqrt (∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n)) = Real.sqrt (2 * Λ2) := by
    rw [h1]
  have hs2 : Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
      ≤ W * Real.sqrt (2 * Λ2) := by
    calc Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
        ≤ Real.sqrt (W ^ 2 * (2 * Λ2)) := Real.sqrt_le_sqrt h2
      _ = W * Real.sqrt (2 * Λ2) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW]
  have hsq : Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2) = 2 * Λ2 :=
    Real.mul_self_sqrt (by positivity)
  have hsnn : 0 ≤ Real.sqrt (2 * Λ2) := Real.sqrt_nonneg _
  constructor
  · rw [hs1]
    calc C * Real.sqrt (2 * Λ2) * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
        ≤ C * Real.sqrt (2 * Λ2) * (W * Real.sqrt (2 * Λ2)) := by gcongr
      _ = C * W * (Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2)) := by ring
      _ = 2 * C * W * Λ2 := by rw [hsq]; ring
  · rw [hs1]
    calc C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n)) * Real.sqrt (2 * Λ2)
        ≤ C * (W * Real.sqrt (2 * Λ2)) * Real.sqrt (2 * Λ2) := by gcongr
      _ = C * W * (Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2)) := by ring
      _ = 2 * C * W * Λ2 := by rw [hsq]; ring
