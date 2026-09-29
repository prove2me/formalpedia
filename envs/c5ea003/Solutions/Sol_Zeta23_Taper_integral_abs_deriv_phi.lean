-- Prove2me | solution 1 for Zeta23.Taper.integral_abs_deriv_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:16:37.417739+00:00
-- url     : https://prove2.me/submissions/2eb459c3-176b-461d-852d-55f80c83d07c

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
import Theorems.Thm_Zeta23_Taper_phi_contDiff

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



/-- `φ(u) = 0` for `|u| ≥ L/2`. -/
theorem phi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phi ϱ L w u = 0 := by
  unfold phi
  apply hϱ.eq_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

/-- `φ = 1` on `[−L/2 + w, L/2 − w]`. -/
theorem phi_eq_one (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : |u| ≤ L / 2 - w) :
    phi ϱ L w u = 1 := by
  unfold phi
  apply hϱ.eq_one
  rw [ge_iff_le, le_div_iff₀ hw]
  linarith







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

/-- A monotone function has nonnegative derivative wherever it is differentiable. -/
lemma deriv_nonneg_of_monotone {f : ℝ → ℝ} (hf : Monotone f) {y : ℝ}
    (hd : DifferentiableAt ℝ f y) : 0 ≤ deriv f y := by
  have h := hd.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at h
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rcases lt_or_gt_of_ne (hx : x ≠ y) with hlt | hgt
  · rw [slope_def_field]
    have h := div_nonneg (show (0 : ℝ) ≤ f y - f x by linarith [hf hlt.le])
      (show (0 : ℝ) ≤ y - x by linarith)
    rwa [show (f y - f x) / (y - x) = (f x - f y) / (x - y) by
      rw [← neg_sub (f x) (f y), ← neg_sub x y, neg_div_neg_eq]] at h
  · rw [slope_def_field]
    exact div_nonneg (by linarith [hf hgt.le]) (by linarith)

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

/-- ∫ℝ |F′| = 2 for an even C¹ bump: F(0) = 1, F = 0 off [−L/2, L/2], F′ ≤ 0 on (0,∞). -/
lemma integral_abs_deriv_eq_two {F : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hF : ContDiff ℝ 1 F) (heven : ∀ u, F (-u) = F u)
    (hnonpos : ∀ u : ℝ, 0 < u → deriv F u ≤ 0)
    (hsupp : ∀ u : ℝ, L / 2 ≤ |u| → F u = 0) (hF0 : F 0 = 1) :
    ∫ u, |deriv F u| = 2 := by
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hodd : ∀ u : ℝ, deriv F (-u) = -(deriv F u) := by
    intro u
    have h1 : deriv (fun x : ℝ => F (-x)) u = -deriv F (-u) := deriv_comp_neg F u
    have h2 : (fun x : ℝ => F (-x)) = F := funext heven
    rw [h2] at h1
    linarith
  have hzero_out : ∀ u : ℝ, L / 2 < |u| → deriv F u = 0 := by
    intro u hu
    have hopen : IsOpen {v : ℝ | L / 2 < |v|} := isOpen_lt continuous_const continuous_abs
    have hev : F =ᶠ[nhds u] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hu] with v hv
      exact hsupp v (le_of_lt hv)
    rw [hev.deriv_eq]
    simp
  have heqIcc : ∫ u, |deriv F u| = ∫ u in Icc (-(L / 2)) (L / 2), |deriv F u| := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    have : L / 2 < |u| := by
      rcases hu with h | h
      · calc L / 2 < -u := by linarith
          _ ≤ |u| := neg_le_abs u
      · calc L / 2 < u := h
          _ ≤ |u| := le_abs_self u
    rw [hzero_out u this, abs_zero]
  have hIccIoc : ∫ u in Icc (-(L / 2)) (L / 2), |deriv F u|
      = ∫ u in (-(L / 2))..(L / 2), |deriv F u| := by
    rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun u => |deriv F u|) MeasureTheory.volume a b :=
    fun a b => (hdcont.abs).intervalIntegrable a b
  have hsplit : ∫ u in (-(L / 2))..(L / 2), |deriv F u|
      = (∫ u in (-(L / 2))..(0 : ℝ), |deriv F u|) + ∫ u in (0 : ℝ)..(L / 2), |deriv F u| :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
  have hright : ∫ u in (0 : ℝ)..(L / 2), |deriv F u| = 1 := by
    have habs : ∫ u in (0 : ℝ)..(L / 2), |deriv F u|
        = ∫ u in (0 : ℝ)..(L / 2), -(deriv F u) := by
      rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le
        (by linarith)]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      exact abs_of_nonpos (hnonpos u hu.1)
    rw [habs, intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hF.differentiable (by norm_num)).differentiableAt) (hdcont.intervalIntegrable _ _)]
    rw [hsupp (L / 2) (by rw [abs_of_pos (by linarith)]), hF0]
    ring
  have hleft : ∫ u in (-(L / 2))..(0 : ℝ), |deriv F u|
      = ∫ u in (0 : ℝ)..(L / 2), |deriv F u| := by
    have h1 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L / 2)
      (fun u => |deriv F u|)
    have h2 : (∫ x in (0 : ℝ)..(L / 2), |deriv F (-x)|)
        = ∫ x in (0 : ℝ)..(L / 2), |deriv F x| := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [hodd, abs_neg]
    rw [← h2, h1]
    norm_num
  rw [heqIcc, hIccIoc, hsplit, hleft, hright]
  ring


























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

theorem solution (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (phi ϱ L w) u| = 2 := by
  refine integral_abs_deriv_eq_two (by linarith) ((phi_contDiff hϱ hw hwL).of_le (by norm_num))
    phi_even (fun u hu => ?_) (fun u hu => phi_eq_zero hϱ hw hu) (phi_eq_one hϱ hw (by
      rw [abs_zero]; linarith))
  rw [deriv_phi_pos hϱ hw hu]
  have h1 : 0 ≤ deriv ϱ ((L / 2 - u) / w) :=
    deriv_nonneg_of_monotone hϱ.monotone (rho_differentiable hϱ _)
  have h2 : 0 ≤ deriv ϱ ((L / 2 - u) / w) / w := div_nonneg h1 hw.le
  linarith
