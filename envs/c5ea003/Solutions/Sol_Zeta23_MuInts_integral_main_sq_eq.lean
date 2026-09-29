-- Prove2me | solution 1 for Zeta23.MuInts.integral_main_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:03:56.684882+00:00
-- url     : https://prove2.me/submissions/b9359499-b86b-4782-a7e4-c3dbc2ee614c

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
import Definitions.Def_Zeta23_GammaFacts_IntMu
import Definitions.Def_Zeta23_GammaFacts_Series

-- from Zeta23.GammaFacts.IntMu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/IntMu.lean — the [eq:muints] Γ-half integrals.
Paper: "∫_T^{2T} μ(τ)dτ = Tℓ₁/(2π) + O(1/T)", "∫_T^{2T} μ(τ)² dτ = (Tℓ₁²/4π²)(1 + O(l⁻²))",
via "(eq:muints) follows from (eq:mufacts) … and ∫_T^{2T} log²(τ/2π) dτ = T(ℓ₁² + 1 − 2log²2)".
Both theorems take the Stirling field as a hypothesis (hst); the Stirling asymptotic itself is
proved elsewhere in the repository, so GammaFacts assembles with no Γ-hypothesis beyond it.
-/

noncomputable section

namespace Zeta23
namespace MuInts

open MeasureTheory intervalIntegral






end MuInts
end Zeta23
end
open Zeta23
open MuInts
open MeasureTheory intervalIntegral

theorem solution {T : ℝ} (hT : 0 < T) :
    ∫ τ in T..(2 * T), Real.log (τ / (2 * Real.pi)) ^ 2
      = T * (ell1 T ^ 2 + 1 - 2 * Real.log 2 ^ 2) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hftc : ∀ τ ∈ Set.uIcc T (2 * T),
      HasDerivAt (fun x : ℝ =>
          x * (Real.log (x / (2 * Real.pi)) ^ 2 - 2 * Real.log (x / (2 * Real.pi)) + 2))
        (Real.log (τ / (2 * Real.pi)) ^ 2) τ := by
    intro τ hτ
    rw [Set.uIcc_of_le (by linarith)] at hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) τ :=
      (hasDerivAt_id τ).div_const _
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi))) (1 / τ) τ := by
      have h3 := (Real.hasDerivAt_log (by positivity : τ / (2 * Real.pi) ≠ 0)).comp τ h1
      have heq : 1 / τ = (τ / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)) := by
        rw [inv_div]
        field_simp
      rw [heq]
      exact h3
    have h4 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)) ^ 2)
        (2 * Real.log (τ / (2 * Real.pi)) * (1 / τ)) τ := by
      have h5 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)) ^ 2)
          ((2 : ℕ) * Real.log (τ / (2 * Real.pi)) ^ (2 - 1) * (1 / τ)) τ := h2.pow 2
      convert h5 using 1
      norm_num
    have h6 : HasDerivAt (fun x : ℝ =>
        Real.log (x / (2 * Real.pi)) ^ 2 - 2 * Real.log (x / (2 * Real.pi)) + 2)
        (2 * Real.log (τ / (2 * Real.pi)) * (1 / τ) - 2 * (1 / τ)) τ := by
      have h7 := (h4.sub (h2.const_mul 2)).add_const 2
      exact h7
    have h8 := (hasDerivAt_id τ).mul h6
    have hτne : τ ≠ 0 := hτ0.ne'
    have heq : Real.log (τ / (2 * Real.pi)) ^ 2
        = 1 * (Real.log (τ / (2 * Real.pi)) ^ 2 - 2 * Real.log (τ / (2 * Real.pi)) + 2)
          + τ * (2 * Real.log (τ / (2 * Real.pi)) * (1 / τ) - 2 * (1 / τ)) := by
      field_simp
      ring
    rw [heq]
    exact h8
  have hcont : IntervalIntegrable
      (fun τ : ℝ => Real.log (τ / (2 * Real.pi)) ^ 2) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    exact (((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).pow 2).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hftc hcont]
  have h2T : Real.log (2 * T / (2 * Real.pi)) = Real.log 2 + Real.log (T / (2 * Real.pi)) := by
    rw [show 2 * T / (2 * Real.pi) = 2 * (T / (2 * Real.pi)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  rw [h2T]
  unfold ell1 l
  ring
