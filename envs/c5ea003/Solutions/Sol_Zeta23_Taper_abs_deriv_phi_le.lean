-- Prove2me | solution 1 for Zeta23.Taper.abs_deriv_phi_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:19:52.823602+00:00
-- url     : https://prove2.me/submissions/0fdff671-090e-4909-8c92-6a8d0ba9ac81

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






/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/

variable (ϱ : ℝ → ℝ) (L w : ℝ)











/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/

section Basic
variable {ϱ L w}

theorem phi_even (u : ℝ) : phi ϱ L w (-u) = phi ϱ L w u := by
  simp [phi, abs_neg]











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

/-- For u > 0, φ′(u) = −ϱ′((L/2 − u)/w)/w. -/
lemma deriv_phi_pos (hϱ : TaperProfile ϱ) (_hw : 0 < w) {u : ℝ} (hu : 0 < u) :
    deriv (phi ϱ L w) u = -(deriv ϱ ((L / 2 - u) / w) / w) := by
  have hev : phi ϱ L w =ᶠ[nhds u] (fun v => ϱ ((L / 2 - v) / w)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    unfold phi
    rw [abs_of_pos hv]
  rw [hev.deriv_eq]
  have hg : HasDerivAt (fun v : ℝ => (L / 2 - v) / w) (-1 / w) u := by
    have h1 : HasDerivAt (fun v : ℝ => L / 2 - v) (-1) u := (hasDerivAt_id u).const_sub (L / 2)
    exact h1.div_const w
  have hϱd : HasDerivAt ϱ (deriv ϱ ((L / 2 - u) / w)) ((L / 2 - u) / w) :=
    (rho_differentiable hϱ _).hasDerivAt
  have hcomp : HasDerivAt (fun v : ℝ => ϱ ((L / 2 - v) / w))
      (deriv ϱ ((L / 2 - u) / w) * (-1 / w)) u := hϱd.comp u hg
  rw [hcomp.deriv]
  ring





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

lemma supDeriv_nonneg (hϱ : TaperProfile ϱ) : 0 ≤ supDeriv ϱ :=
  le_trans (abs_nonneg _) (abs_derivRho_le hϱ 0)


lemma deriv_phi_odd (_hϱ : TaperProfile ϱ) (v : ℝ) :
    deriv (phi ϱ L w) (-v) = -(deriv (phi ϱ L w) v) := by
  have h1 : deriv (fun x : ℝ => phi ϱ L w (-x)) v = -deriv (phi ϱ L w) (-v) :=
    deriv_comp_neg _ _
  have h2 : (fun x : ℝ => phi ϱ L w (-x)) = phi ϱ L w := funext fun x => phi_even x
  rw [h2] at h1
  linarith













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

theorem solution (hϱ : TaperProfile ϱ) (hw : 0 < w) (_hwL : 2 * w ≤ L) (u : ℝ) :
    |deriv (phi ϱ L w) u| ≤ supDeriv ϱ / w := by
  have key : ∀ v : ℝ, 0 < v → |deriv (phi ϱ L w) v| ≤ supDeriv ϱ / w := by
    intro v hv
    rw [deriv_phi_pos hϱ hw hv, abs_neg, abs_div, abs_of_pos hw]
    gcongr
    exact abs_derivRho_le hϱ _
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have heq : deriv (phi ϱ L w) u = -(deriv (phi ϱ L w) (-u)) := by
      have := deriv_phi_odd hϱ (L := L) (w := w) (-u)
      rwa [neg_neg] at this
    rw [heq, abs_neg]
    exact key (-u) (by linarith)
  · subst hu
    have h0 : deriv (phi ϱ L w) 0 = 0 := by
      have := deriv_phi_odd hϱ (L := L) (w := w) 0
      rw [neg_zero] at this
      linarith
    rw [h0, abs_zero]
    have := supDeriv_nonneg hϱ
    positivity
  · exact key u hu
