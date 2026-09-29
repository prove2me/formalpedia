-- Prove2me | solution 1 for Zeta23.Taper.integral_abs_deriv2_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:18:15.2409+00:00
-- url     : https://prove2.me/submissions/81e9d32a-eb12-4a81-b64d-ad6107cc05de

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

lemma derivRho2_zero_left (hϱ : TaperProfile ϱ) {x : ℝ} (hx : x < 0) :
    deriv (deriv ϱ) x = 0 := by
  have hev : deriv ϱ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with v hv
    exact derivRho_zero_left hϱ hv
  rw [hev.deriv_eq]
  simp

lemma derivRho2_zero_right (hϱ : TaperProfile ϱ) {x : ℝ} (hx : 1 < x) :
    deriv (deriv ϱ) x = 0 := by
  have hev : deriv ϱ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with v hv
    exact derivRho_zero_right hϱ hv
  rw [hev.deriv_eq]
  simp






lemma deriv_phi_odd (_hϱ : TaperProfile ϱ) (v : ℝ) :
    deriv (phi ϱ L w) (-v) = -(deriv (phi ϱ L w) v) := by
  have h1 : deriv (fun x : ℝ => phi ϱ L w (-x)) v = -deriv (phi ϱ L w) (-v) :=
    deriv_comp_neg _ _
  have h2 : (fun x : ℝ => phi ϱ L w (-x)) = phi ϱ L w := funext fun x => phi_even x
  rw [h2] at h1
  linarith


/-- For u > 0, φ″(u) = ϱ″((L/2 − u)/w)/w². -/
lemma deriv2_phi_pos (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : 0 < u) :
    deriv (deriv (phi ϱ L w)) u = deriv (deriv ϱ) ((L / 2 - u) / w) / w ^ 2 := by
  have hev : deriv (phi ϱ L w) =ᶠ[nhds u] (fun v => -(deriv ϱ ((L / 2 - v) / w) / w)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact deriv_phi_pos hϱ hw hv
  rw [hev.deriv_eq]
  have hg : HasDerivAt (fun v : ℝ => (L / 2 - v) / w) (-1 / w) u := by
    have h1 : HasDerivAt (fun v : ℝ => L / 2 - v) (-1) u := (hasDerivAt_id u).const_sub (L / 2)
    exact h1.div_const w
  have hd2 : HasDerivAt (deriv ϱ) (deriv (deriv ϱ) ((L / 2 - u) / w)) ((L / 2 - u) / w) :=
    ((hϱ.contDiff.deriv' (n := 2)).differentiable (by norm_num) _).hasDerivAt
  have hcomp0 : HasDerivAt ((deriv ϱ) ∘ fun v : ℝ => (L / 2 - v) / w)
      (deriv (deriv ϱ) ((L / 2 - u) / w) * (-1 / w)) u := hd2.comp u hg
  have hcomp : HasDerivAt (fun v : ℝ => deriv ϱ ((L / 2 - v) / w))
      (deriv (deriv ϱ) ((L / 2 - u) / w) * (-1 / w)) u := hcomp0
  have hneg : HasDerivAt (fun v : ℝ => -(deriv ϱ ((L / 2 - v) / w) / w))
      (-(deriv (deriv ϱ) ((L / 2 - u) / w) * (-1 / w) / w)) u := (hcomp.div_const w).neg
  rw [hneg.deriv]
  field_simp

/-- Even-integrand reduction: ∫ℝ |G| = 2∫₀^{L/2} |G| for |G| even, G = 0 off [−L/2, L/2]. -/
lemma integral_abs_eq_two_mul {G : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hcont : Continuous G)
    (habs_even : ∀ u, |G (-u)| = |G u|) (hzero : ∀ u : ℝ, L / 2 < |u| → G u = 0) :
    ∫ u, |G u| = 2 * ∫ u in (0 : ℝ)..(L / 2), |G u| := by
  have heqIcc : ∫ u, |G u| = ∫ u in Icc (-(L / 2)) (L / 2), |G u| := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    have habs : L / 2 < |u| := by
      rcases hu with h | h
      · calc L / 2 < -u := by linarith
          _ ≤ |u| := neg_le_abs u
      · calc L / 2 < u := h
          _ ≤ |u| := le_abs_self u
    rw [hzero u habs, abs_zero]
  have hIccIoc : ∫ u in Icc (-(L / 2)) (L / 2), |G u|
      = ∫ u in (-(L / 2))..(L / 2), |G u| := by
    rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun u => |G u|) MeasureTheory.volume a b :=
    fun a b => (hcont.abs).intervalIntegrable a b
  have hsplit : ∫ u in (-(L / 2))..(L / 2), |G u|
      = (∫ u in (-(L / 2))..(0 : ℝ), |G u|) + ∫ u in (0 : ℝ)..(L / 2), |G u| :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
  have hleft : ∫ u in (-(L / 2))..(0 : ℝ), |G u| = ∫ u in (0 : ℝ)..(L / 2), |G u| := by
    have h1 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L / 2)
      (fun u => |G u|)
    have h2 : (∫ x in (0 : ℝ)..(L / 2), |G (-x)|) = ∫ x in (0 : ℝ)..(L / 2), |G x| :=
      intervalIntegral.integral_congr fun x _ => habs_even x
    rw [← h2, h1]
    norm_num
  rw [heqIcc, hIccIoc, hsplit, hleft]
  ring

lemma deriv_phi_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (deriv (phi ϱ L w)) :=
  (phi_contDiff hϱ hw hwL).deriv' (n := 2)

lemma deriv2_phi_even (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (v : ℝ) :
    deriv (deriv (phi ϱ L w)) (-v) = deriv (deriv (phi ϱ L w)) v := by
  have h1 : deriv (fun x : ℝ => deriv (phi ϱ L w) (-x)) v
      = -deriv (deriv (phi ϱ L w)) (-v) := deriv_comp_neg _ _
  have h2 : (fun x : ℝ => deriv (phi ϱ L w) (-x)) = fun x => -(deriv (phi ϱ L w) x) :=
    funext (deriv_phi_odd hϱ)
  rw [h2] at h1
  have h3 : deriv (fun x : ℝ => -(deriv (phi ϱ L w) x)) v
      = -(deriv (deriv (phi ϱ L w)) v) :=
    ((((deriv_phi_contDiff hϱ hw hwL).differentiable (by norm_num)) v).hasDerivAt.neg).deriv
  rw [h3] at h1
  linarith

lemma deriv2_phi_zero_out (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ}
    (hu : L / 2 < |u|) : deriv (deriv (phi ϱ L w)) u = 0 := by
  have hopen : IsOpen {v : ℝ | L / 2 < |v|} := isOpen_lt continuous_const continuous_abs
  have hev : deriv (phi ϱ L w) =ᶠ[nhds u] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hu] with v hv
    have hφ0 : phi ϱ L w =ᶠ[nhds v] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hv] with x hx
      exact phi_eq_zero hϱ hw (le_of_lt hx)
    rw [hφ0.deriv_eq]
    simp
  rw [hev.deriv_eq]
  simp







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
    ∫ u, |deriv (deriv (phi ϱ L w)) u| = 2 * l1Deriv2 ϱ / w := by
  have hL : (0 : ℝ) < L := by linarith
  have hcont2 : Continuous (deriv (deriv (phi ϱ L w))) :=
    (deriv_phi_contDiff hϱ hw hwL).continuous_deriv (by norm_num)
  rw [integral_abs_eq_two_mul hL hcont2
    (fun u => by rw [deriv2_phi_even hϱ hw hwL]) (fun u hu => deriv2_phi_zero_out hϱ hw hu)]
  have hcongr : ∫ u in (0 : ℝ)..(L / 2), |deriv (deriv (phi ϱ L w)) u|
      = ∫ u in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) ((L / 2 - u) / w)| / w ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le
      (by linarith)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [deriv2_phi_pos hϱ hw hu.1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < w ^ 2)]
  rw [hcongr]
  have hsub1 : ∫ u in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) ((L / 2 - u) / w)| / w ^ 2
      = ∫ y in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) (y / w)| / w ^ 2 := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := L / 2)
      (fun y => |deriv (deriv ϱ) (y / w)| / w ^ 2) (L / 2)
    simpa using h
  rw [hsub1]
  have hdiv : ∫ y in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) (y / w)| / w ^ 2
      = (∫ y in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) (y / w)|) / w ^ 2 :=
    intervalIntegral.integral_div _ _
  rw [hdiv]
  have hsub2 : ∫ y in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) (y / w)|
      = w * ∫ y in (0 : ℝ)..(L / (2 * w)), |deriv (deriv ϱ) y| := by
    have h := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := L / 2)
      (f := fun y => |deriv (deriv ϱ) y|) (ne_of_gt hw)
    rw [h, smul_eq_mul]
    norm_num [div_div]
  rw [hsub2]
  have hfull : ∫ y in (0 : ℝ)..(L / (2 * w)), |deriv (deriv ϱ) y| = l1Deriv2 ϱ := by
    have hone : (1 : ℝ) ≤ L / (2 * w) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    unfold l1Deriv2
    rw [intervalIntegral.integral_of_le (by linarith),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm.symm
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [derivRho2_zero_left hϱ h, abs_zero]
    · rw [derivRho2_zero_right hϱ (by linarith), abs_zero]
  rw [hfull]
  field_simp
