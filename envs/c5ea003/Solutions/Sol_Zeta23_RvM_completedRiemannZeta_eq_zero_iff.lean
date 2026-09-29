-- Prove2me | solution 1 for Zeta23.RvM.completedRiemannZeta_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:54:55.504095+00:00
-- url     : https://prove2.me/submissions/f2eb90aa-7cbf-4906-98c6-548ba4d7d233

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv

-- from Zeta23.RvM.CountByIntegral
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/CountByIntegral.lean — the zero count as a contour integral, specialised to Λ.
Used by Zeta23/RvM/Statement.lean and MainTerm.lean (the symmetry fold and the Γ-side).

MAIN RESULT `rectangleIntegral'_logDeriv_completedZeta_eq_Ncount`: for 0 < T₁ ≤ T₂, neither the
ordinate of a nontrivial zero,
    (1/2πi) ∮_{∂([−1,2]×[T₁,T₂])} Λ'/Λ(s) ds = N(T₁,T₂)        (Λ = completedRiemannZeta),
where N = Zeta23.Ncount counts nontrivial zeros of Mathlib's riemannZeta with T₁ < γ ≤ T₂ with
multiplicity zeroMult = analyticOrderAt ζ. Ingredients (all proved here from Mathlib):
 • Λ is analytic off {0,1}; Λ = Gammaℝ·ζ with Gammaℝ ≠ 0 on Re s > 0, so on the strip the zeros
   and their analytic orders agree with ζ's; Λ ≠ 0 for Re s ≥ 1 (Mathlib's non-vanishing of ζ)
   and, by Λ(1−s) = Λ(s), for Re s ≤ 0; hence {Λ = 0} = nontrivial zeros of ζ exactly.
 • Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (weighted argument principle, g ≡ 1).
-/

open Complex Set Topology Filter Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Λ = completedRiemannZeta: analyticity, relation to ζ, zeros -/


lemma completedRiemannZeta_eq_Gammaℝ_mul {s : ℂ} (hs : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp

lemma completedRiemannZeta_eq_zero_iff_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  rw [completedRiemannZeta_eq_Gammaℝ_mul h0 hG, mul_eq_zero]
  simp [hG]

lemma completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  rw [Ne, completedRiemannZeta_eq_zero_iff_of_re_pos (by linarith)]
  exact riemannZeta_ne_zero_of_one_le_re hs

lemma completedRiemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  exact completedRiemannZeta_ne_zero_of_one_le_re (by simp; linarith)



/-! ## The count -/


end RvM
end Zeta23
end
open Complex Set Topology Filter Real
open Zeta23
open RvM

theorem solution {s : ℂ} :
    completedRiemannZeta s = 0 ↔ IsNontrivialZero s := by
  constructor
  · intro h
    have h1 : 0 < s.re := by
      by_contra hle
      exact completedRiemannZeta_ne_zero_of_re_nonpos (not_lt.mp hle) h
    have h2 : s.re < 1 := by
      by_contra hle
      exact completedRiemannZeta_ne_zero_of_one_le_re (not_lt.mp hle) h
    exact ⟨(completedRiemannZeta_eq_zero_iff_of_re_pos h1).mp h, h1, h2⟩
  · rintro ⟨hz, h1, _⟩
    exact (completedRiemannZeta_eq_zero_iff_of_re_pos h1).mpr hz
