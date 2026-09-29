-- Prove2me | solution 1 for Zeta23.WeilEF.logDeriv_completedZeta_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:41:50.254709+00:00
-- url     : https://prove2.me/submissions/0ad76940-3af7-4359-bc79-a7a933ee313f

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement

-- from Zeta23.WeilEF.XiLogDeriv
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/XiLogDeriv.lean
The completed zeta function Λ = completedRiemannZeta: log-derivative decomposition, functional equation
for logDeriv, zeros in the strip = nontrivial zeros of ζ with equal analytic order.

Mathlib normalization (verified): for s ≠ 0, riemannZeta s = completedRiemannZeta s / Gammaℝ s
(riemannZeta_def_of_ne_zero) and Gammaℝ s ≠ 0 for 0 < Re s (Gammaℝ_ne_zero_of_re_pos); hence on the
open right half-plane Λ = Γℝ · ζ on the nose (completedZeta_eventuallyEq_mul) — no pole bookkeeping is
needed for the three statements below (Λ's poles at 0, 1 are excluded by hypothesis).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Filter Topology








end WeilEF
end Zeta23
end
open Zeta23
open Complex Filter Topology

theorem solution (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  have hcomp : completedRiemannZeta = completedRiemannZeta ∘ (fun u : ℂ => 1 - u) := by
    funext u; simp [completedRiemannZeta_one_sub]
  have hd : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta (sub_ne_zero.mpr (Ne.symm hs1)) (by
      intro h; apply hs0; linear_combination -h)
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) s := (differentiableAt_const _).sub differentiableAt_id
  have key := logDeriv_comp (x := s) hd hg
  rw [← hcomp] at key
  have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [key, hderiv]
  ring
