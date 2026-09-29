-- Prove2me | solution 1 for Zeta23.RvM.mu_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:37:52.276555+00:00
-- url     : https://prove2.me/submissions/703e8508-25cd-486c-bc02-5d7481dbd73a

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_RvM_GammaSide
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

-- from Zeta23.RvM.GammaSide
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/GammaSide.lean — the Γ-factor side of the folded contour is
EXACTLY the paper's ∫μ:  (1/π)·Im ∫_L Γℝ'/Γℝ ds = ∫_{T₁}^{T₂} μ(t) dt  for 0 < T₁,
because Γℝ'/Γℝ is holomorphic on Re s > 0 (Cauchy–Goursat on [½,2]×[T₁,T₂] moves L to the critical-line
segment) and Re Γℝ'/Γℝ(½+it) = ½ Re ψ(¼+it/2) − ½ log π = π·μ(t)  (Γℝ(s) = π^{−s/2}Γ(s/2), μ = Zeta23.mu).
-/

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

namespace Zeta23.RvM










/-! ### helpers for the assembly -/



end Zeta23.RvM
end
open Complex MeasureTheory Set
open scoped Interval
open Zeta23
open Zeta23.RvM

theorem solution (hΓ : Zeta23.GammaFacts) : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 1 ≤ τ →
    |mu τ| ≤ C * Real.log (τ + 3) := by
  obtain ⟨C₀, hC₀⟩ := hΓ.stirling
  have hlog2π : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine ⟨1 + |C₀| + Real.log (2 * Real.pi),
    by linarith [abs_nonneg C₀], fun τ hτ => ?_⟩
  have hτ0 : (0:ℝ) < τ := by linarith
  have h1 := hC₀ τ (by rw [abs_of_pos hτ0]; exact hτ)
  rw [abs_of_pos hτ0] at h1
  obtain ⟨hl, hr⟩ := abs_le.mp h1
  have hlog3 : 1 ≤ Real.log (τ + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlogτ0 : 0 ≤ Real.log τ := Real.log_nonneg hτ
  have hlogτ : Real.log τ ≤ Real.log (τ + 3) := Real.log_le_log hτ0 (by linarith)
  have hdiv : Real.log (τ / (2 * Real.pi)) = Real.log τ - Real.log (2 * Real.pi) :=
    Real.log_div (by linarith) (by positivity)
  rw [hdiv] at hl hr
  have hC₀τ : |C₀ / τ ^ 2| ≤ |C₀| := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < τ ^ 2)]
    apply div_le_self (abs_nonneg _) (by nlinarith)
  obtain ⟨hCl, hCr⟩ := abs_le.mp hC₀τ
  have h2π : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have h2π0 : 0 < 1 / (2 * Real.pi) := by positivity
  rw [abs_le]
  constructor
  · -- lower bound: mu τ ≥ (1/2π)(log τ − log 2π) − C₀/τ² ≥ −(…)·log(τ+3)
    have e1 : -(Real.log (2 * Real.pi)) ≤ 1 / (2 * Real.pi) * (Real.log τ - Real.log (2 * Real.pi)) := by
      nlinarith
    nlinarith
  · have e2 : 1 / (2 * Real.pi) * (Real.log τ - Real.log (2 * Real.pi)) ≤ Real.log (τ + 3) := by
      nlinarith
    nlinarith
