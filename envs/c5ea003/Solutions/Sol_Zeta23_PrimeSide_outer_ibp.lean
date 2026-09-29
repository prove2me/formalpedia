-- Prove2me | solution 1 for Zeta23.PrimeSide.outer_ibp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:36:41.354161+00:00
-- url     : https://prove2.me/submissions/78bfc08a-fe20-47e6-83cf-c0fb7aeab9f7

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

-- from Zeta23.PrimeSideA.CrossMuPCore
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Analytic core of [prop:cross] (i): the double integration by parts for `𝓜[u, cos(·y)]`

See `Zeta23/PrimeSideA/CrossMuP.lean` for the statement of [prop:cross](i) and the paper text.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

section CrossMuPCore
variable {Φ : ℝ → ℝ} {T : ℝ}










end CrossMuPCore

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem solution (hΦ : ContDiff ℝ 1 Φ) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (τ' : ℝ) :
    ∫ τ in T..(2 * T), u τ * deriv (fun x => Φ x ^ 2) (τ - τ')
      = u (2 * T) * Φ (2 * T - τ') ^ 2 - u T * Φ (T - τ') ^ 2
        - ∫ τ in T..(2 * T), deriv u τ * Φ (τ - τ') ^ 2 := by
  set Ψ : ℝ → ℝ := fun x => Φ x ^ 2 with hΨdef
  have hΨ : ContDiff ℝ 1 Ψ := hΦ.pow 2
  have hΨd : ∀ x, HasDerivAt Ψ (deriv Ψ x) x := fun x =>
    (hΨ.differentiable one_ne_zero x).hasDerivAt
  have hΨ'c : Continuous (deriv Ψ) := hΨ.continuous_deriv le_rfl
  have hud : ∀ x ∈ uIcc T (2 * T), HasDerivAt u (deriv u x) x := fun x _ =>
    (hu.differentiable one_ne_zero x).hasDerivAt
  have hu'c : Continuous (deriv u) := hu.continuous_deriv le_rfl
  have hv : ∀ x ∈ uIcc T (2 * T), HasDerivAt (fun τ => Ψ (τ - τ')) (deriv Ψ (x - τ')) x := by
    intro x _
    have h := (hΨd (x - τ')).comp x ((hasDerivAt_id x).sub_const τ')
    simpa [Function.comp_def] using h
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hud hv
    (hu'c.intervalIntegrable _ _)
    ((hΨ'c.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _)
  simp only [hΨdef] at hibp ⊢
  rw [hibp]
