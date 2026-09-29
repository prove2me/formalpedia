-- Prove2me | solution 1 for Zeta23.PrimeSide.inv_two_mul_le_abs_log_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:32:16.833001+00:00
-- url     : https://prove2.me/submissions/c61400cd-1252-4b26-b943-95f28c0d1323

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
variable {C : ℝ}

theorem solution {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    1 / (2 * (n:ℝ)) ≤ |Real.log n - Real.log m| := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hnm with h | h
  · -- n < m:  log m − log n ≥ 1 − n/m = (m−n)/m ≥ 1/(2n)
    have hm1 : (n:ℝ) + 1 ≤ m := by exact_mod_cast h
    have hlog : 1 - ((m:ℝ) / n)⁻¹ ≤ Real.log ((m:ℝ) / n) :=
      Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [inv_div, Real.log_div hm0.ne' hn0.ne'] at hlog
    have h2 : 1 / (2 * (n:ℝ)) ≤ (m - n) / m := by
      rw [div_le_div_iff₀ (by positivity) hm0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (by linarith : (0:ℝ) ≤ 2 * n - 1)]
    have h3 : ((m:ℝ) - n) / m = 1 - n / m := by field_simp
    rw [abs_sub_comm, abs_of_nonneg (by
      linarith [Real.log_le_log hn0 (by linarith : (n:ℝ) ≤ m)])]
    linarith
  · -- m < n:  log n − log m ≥ 1 − m/n = (n−m)/n ≥ 1/n ≥ 1/(2n)
    have hm1 : (m:ℝ) + 1 ≤ n := by exact_mod_cast h
    have hlog : 1 - ((n:ℝ) / m)⁻¹ ≤ Real.log ((n:ℝ) / m) :=
      Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [inv_div, Real.log_div hn0.ne' hm0.ne'] at hlog
    have h2 : 1 / (2 * (n:ℝ)) ≤ (n - m) / n := by
      rw [div_le_div_iff₀ (by positivity) hn0]
      nlinarith
    have h3 : ((n:ℝ) - m) / n = 1 - m / n := by field_simp
    rw [abs_of_nonneg (by linarith [Real.log_le_log hm0 (by linarith : (m:ℝ) ≤ n)])]
    linarith
