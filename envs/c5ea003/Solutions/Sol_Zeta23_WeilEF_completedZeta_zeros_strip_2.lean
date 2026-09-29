-- Prove2me | solution 2 for Zeta23.WeilEF.completedZeta_zeros_strip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:42:59.338885+00:00
-- url     : https://prove2.me/submissions/ddd35d5e-781e-4881-b815-f9893925b51d

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
import Theorems.Thm_Zeta23_WeilEF_differentiableAt_GammaR

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


/-- Γℝ is analytic at every point of the right half-plane. -/
lemma analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt (fun u hu => (differentiableAt_GammaR hu).differentiableWithinAt)
    (hopen.mem_nhds hs)

/-- On the right half-plane, Λ = Γℝ · ζ (as germs). -/
lemma completedZeta_eventuallyEq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u => Gammaℝ u * riemannZeta u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hΓ := Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp

/-- ζ is analytic at every s ≠ 1. -/
lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    (fun _ hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)




end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex Filter Topology

theorem solution {ρ : ℂ} (h : 0 < ρ.re) (h' : ρ.re < 1) :
    (completedRiemannZeta ρ = 0 ↔ IsNontrivialZero ρ) ∧
    analyticOrderAt completedRiemannZeta ρ = analyticOrderAt riemannZeta ρ := by
  have hρ1 : ρ ≠ 1 := fun e => by simp [e] at h'
  have hΓ : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos h
  have hev := completedZeta_eventuallyEq_mul h
  have hval : completedRiemannZeta ρ = Gammaℝ ρ * riemannZeta ρ := hev.eq_of_nhds
  have hΓan := analyticAt_Gammaℝ h
  have hζan := analyticAt_riemannZeta hρ1
  refine ⟨?_, ?_⟩
  · rw [hval, mul_eq_zero, IsNontrivialZero]
    constructor
    · rintro (hΓ0 | hz)
      · exact absurd hΓ0 hΓ
      · exact ⟨hz, h, h'⟩
    · rintro ⟨hz, -, -⟩
      exact Or.inr hz
  · rw [analyticOrderAt_congr hev]
    have hmul := analyticOrderAt_mul hΓan hζan
    rw [show (Gammaℝ * riemannZeta) = (fun u => Gammaℝ u * riemannZeta u) from rfl] at hmul
    rw [hmul, hΓan.analyticOrderAt_eq_zero.mpr hΓ, zero_add]
