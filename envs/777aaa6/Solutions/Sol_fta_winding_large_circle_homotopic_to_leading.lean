-- Prove2me | solution 1 for fta_winding_large_circle_homotopic_to_leading
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-03T21:40:32.506281+00:00
-- url     : https://prove2.me/submissions/77c85df6-d82e-4de2-ae5e-4f01ac0489f6

import Theorems.Thm_fta_winding_large_circle_homotopic_to_leading
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section
open Complex
open scoped Real unitInterval

private lemma ftaNorm_coe {z : ℂ} (hz : z ≠ 0) : (FtaNormalize z : ℂ) = z / (‖z‖ : ℂ) := by
  rw [FtaNormalize, dif_neg hz]

private lemma ftaNorm_ofReal_pos {r : ℝ} (hr : 0 < r) : FtaNormalize (r : ℂ) = 1 := by
  have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  apply Circle.coe_injective
  rw [ftaNorm_coe hne, Circle.coe_one, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hne]

private lemma ftaNorm_coe_circle (w : Circle) : FtaNormalize (w : ℂ) = w := by
  have hne : (w : ℂ) ≠ 0 := by
    have h1 := Circle.norm_coe w
    intro h; rw [h, norm_zero] at h1; norm_num at h1
  apply Circle.coe_injective
  rw [ftaNorm_coe hne, Circle.norm_coe]
  simp

private lemma ftaNorm_mul {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    FtaNormalize (a * b) = FtaNormalize a * FtaNormalize b := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hna : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  have hnb : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb
  apply Circle.coe_injective
  rw [Circle.coe_mul, ftaNorm_coe hab, ftaNorm_coe ha, ftaNorm_coe hb, norm_mul]
  push_cast
  field_simp

private lemma ftaNorm_continuous {X : Type*} [TopologicalSpace X] {h : X → ℂ}
    (hcont : Continuous h) (hne : ∀ x, h x ≠ 0) :
    Continuous (fun x => FtaNormalize (h x)) := by
  have hco : Continuous (fun x => ((FtaNormalize (h x) : Circle) : ℂ)) := by
    have heq : (fun x => ((FtaNormalize (h x) : Circle) : ℂ)) = fun x => h x / (‖h x‖ : ℂ) :=
      funext fun x => ftaNorm_coe (hne x)
    rw [heq]
    apply hcont.div (Complex.continuous_ofReal.comp hcont.norm)
    intro x; simpa using hne x
  exact Topology.IsInducing.subtypeVal.continuous_iff.mpr hco

open Polynomial in
theorem solution (f : Polynomial ℂ) (R : ℝ) (hR : 0 < R)
    (hdom : FtaLeadingDominatesOnBoundary f R) :
    FtaCircleHomotopic (FtaBoundaryLoop f R)
      (FtaLeadingLoop (FtaLeadingCoeffCircle f) f.natDegree) := by
  obtain ⟨hbn, hseg⟩ := hdom
  set n := f.natDegree with hn
  have hbp : Continuous (fun θ : FtaCircle => FtaBoundaryPoint R θ) := by
    unfold FtaBoundaryPoint
    exact continuous_const.mul
      (continuous_subtype_val.comp (AddCircle.homeomorphCircle').continuous)
  have ha : Continuous (fun θ : FtaCircle => f.eval (FtaBoundaryPoint R θ)) :=
    f.continuous.comp hbp
  have hL : Continuous (fun θ : FtaCircle => FtaLeadingTermBoundary f R θ) := by
    unfold FtaLeadingTermBoundary
    exact continuous_const.mul (hbp.pow n)
  set inner : ↥unitInterval × FtaCircle → ℂ := fun p =>
    (1 - ((p.1 : ℝ) : ℂ)) * f.eval (FtaBoundaryPoint R p.2)
      + ((p.1 : ℝ) : ℂ) * FtaLeadingTermBoundary f R p.2 with hinner
  have hcoeI : Continuous (fun p : ↥unitInterval × FtaCircle => (((p.1 : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have hinner_cont : Continuous inner := by
    apply Continuous.add
    · exact (continuous_const.sub hcoeI).mul (ha.comp continuous_snd)
    · exact hcoeI.mul (hL.comp continuous_snd)
  have hinner_ne : ∀ p : ↥unitInterval × FtaCircle, inner p ≠ 0 := by
    rintro ⟨t, θ⟩; exact hseg θ t
  refine ⟨⟨fun p => FtaNormalize (inner p), ftaNorm_continuous hinner_cont hinner_ne⟩, ?_, ?_⟩
  · intro θ
    simp only [ContinuousMap.coe_mk]
    have e0 : ((0 : ↥unitInterval) : ℝ) = 0 := by norm_num
    have h0 : inner (0, θ) = f.eval (FtaBoundaryPoint R θ) := by
      simp only [hinner, e0, Complex.ofReal_zero, sub_zero, one_mul, zero_mul, add_zero]
    rw [h0]; rfl
  · intro θ
    simp only [ContinuousMap.coe_mk]
    set w : Circle := AddCircle.homeomorphCircle' θ with hw
    have hf0 : f ≠ 0 := fun h => hbn θ (by simp [h])
    have hlc0 : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
    have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hRpn : ((R : ℂ)) ^ n ≠ 0 := pow_ne_zero _ hRne
    have hwne : ((w : ℂ)) ≠ 0 := by
      have := Circle.norm_coe w; intro hh; rw [hh, norm_zero] at this; norm_num at this
    have hwpn : ((w : ℂ)) ^ n ≠ 0 := pow_ne_zero _ hwne
    have e1 : ((1 : ↥unitInterval) : ℝ) = 1 := by norm_num
    have h1 : inner (1, θ) = f.leadingCoeff * ((R : ℂ) ^ n * (w : ℂ) ^ n) := by
      simp only [hinner, e1, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add]
      show FtaLeadingTermBoundary f R θ = _
      unfold FtaLeadingTermBoundary FtaBoundaryPoint
      rw [mul_pow]
    rw [h1, ftaNorm_mul hlc0 (mul_ne_zero hRpn hwpn), ftaNorm_mul hRpn hwpn,
      show ((R : ℂ)) ^ n = (((R ^ n : ℝ)) : ℂ) by push_cast; ring,
      ftaNorm_ofReal_pos (pow_pos hR n),
      show ((w : ℂ)) ^ n = (((w ^ n : Circle)) : ℂ) by push_cast; ring,
      ftaNorm_coe_circle]
    simp only [FtaLeadingCoeffCircle, FtaLeadingLoop, one_mul, hw]
