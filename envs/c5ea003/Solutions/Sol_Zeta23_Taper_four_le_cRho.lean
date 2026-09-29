-- Prove2me | solution 1 for Zeta23.Taper.four_le_cRho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:58:18.188476+00:00
-- url     : https://prove2.me/submissions/06ce6748-4e1b-445a-9ec2-be9b4eede142

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic

-- from Zeta23.Taper.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Basic.lean.  Definitions of the test family
[subsec:family] for generic parameters (ϱ : ℝ → ℝ) (L w : ℝ), and the basic facts of the sentence
after [eq:phidef].  Bodies are literally those of Zeta23/Defs.lean so that
P.phi T = Taper.phi P.ϱ (P.L T) P.w etc. are rfl (bridges in Zeta23/Taper.lean).

Sub-file map (umbrella = Zeta23/Taper.lean):
  Basic   — defs, support/plateau/evenness/C³
  Norms   — [eq:phinorms], [eq:abdef], c_ϱ, C₁, smoothstep
  Strip   — [eq:hfbound] specialized to φ
  Decay   — [eq:gbounds], [eq:psidef], [eq:psiints]
  Fourier — φ̂, Φ real/even/continuous, [eq:PhigA] facts, Plancherel, [eq:Phi2FT]
  Zeta23/Taper.lean — umbrella + the consumer-facing `Params` layer
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23




namespace Taper

/-! ### Constants depending only on ϱ  [eq:phinorms] -/




theorem cRho_eq (ϱ : ℝ → ℝ) : cRho ϱ = 4 * supDeriv ϱ + 4 * l1Deriv2 ϱ := rfl


/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/

variable (ϱ : ℝ → ℝ) (L w : ℝ)











/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/

section Basic
variable {ϱ L w}












end Basic



end Taper

end Zeta23
end

-- from Zeta23.Taper.Norms
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper


/-! ### [eq:phinorms] -/

section Norms
variable {ϱ : ℝ → ℝ} {L w : ℝ}


lemma rho_differentiable (hϱ : TaperProfile ϱ) : Differentiable ℝ ϱ :=
  hϱ.contDiff.differentiable (by norm_num)






/-- deriv ϱ vanishes left of 0 (ϱ is locally 0 there). -/
lemma derivRho_zero_left (hϱ : TaperProfile ϱ) {x : ℝ} (hx : x < 0) : deriv ϱ x = 0 := by
  have hev : ϱ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with v hv
    exact hϱ.eq_zero v (le_of_lt hv)
  rw [hev.deriv_eq]
  simp

/-- deriv ϱ vanishes right of 1 (ϱ is locally 1 there). -/
lemma derivRho_zero_right (hϱ : TaperProfile ϱ) {x : ℝ} (hx : 1 < x) : deriv ϱ x = 0 := by
  have hev : ϱ =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with v hv
    exact hϱ.eq_one v (le_of_lt hv)
  rw [hev.deriv_eq]
  simp



lemma derivRho_continuous (hϱ : TaperProfile ϱ) : Continuous (deriv ϱ) :=
  hϱ.contDiff.continuous_deriv (by norm_num)

lemma bddAbove_abs_derivRho (hϱ : TaperProfile ϱ) :
    BddAbove (Set.range fun x => |deriv ϱ x|) := by
  have hcs : HasCompactSupport (deriv ϱ) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      fun x hx => ?_
    rw [Function.mem_support] at hx
    by_contra h
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact hx (derivRho_zero_left hϱ h)
    · exact hx (derivRho_zero_right hϱ h)
  exact (derivRho_continuous hϱ).abs.bddAbove_range_of_hasCompactSupport
    (hcs.comp_left (g := fun t => |t|) abs_zero)

lemma abs_derivRho_le (hϱ : TaperProfile ϱ) (y : ℝ) : |deriv ϱ y| ≤ supDeriv ϱ :=
  le_ciSup (bddAbove_abs_derivRho hϱ) y


lemma l1Deriv2_nonneg (ϱ : ℝ → ℝ) : 0 ≤ l1Deriv2 ϱ :=
  MeasureTheory.integral_nonneg fun _ => abs_nonneg _














end Norms

/-! ### [eq:abdef]: "`1 − 2w/L ≤ b ≤ a ≤ 1`" -/

section AB
variable {ϱ : ℝ → ℝ} {L w : ℝ}







end AB


end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) : 4 ≤ cRho ϱ := by
  have hl1 := l1Deriv2_nonneg ϱ
  have hftc : ∫ y in (0 : ℝ)..1, deriv ϱ y = 1 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => rho_differentiable hϱ x)
      ((derivRho_continuous hϱ).intervalIntegrable _ _)]
    rw [hϱ.eq_one 1 le_rfl, hϱ.eq_zero 0 le_rfl]
    ring
  have hone : (1 : ℝ) ≤ supDeriv ϱ := by
    have hle : ∫ y in (0 : ℝ)..1, deriv ϱ y ≤ ∫ y in (0 : ℝ)..1, supDeriv ϱ := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((derivRho_continuous hϱ).intervalIntegrable _ _) intervalIntegrable_const
        fun x _ => ?_
      exact le_trans (le_abs_self _) (abs_derivRho_le hϱ x)
    rw [hftc] at hle
    simpa using hle
  rw [cRho_eq]
  linarith
