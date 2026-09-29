-- Prove2me | solution 1 for fta_winding_rootless_boundary_has_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-03T21:44:51.309771+00:00
-- url     : https://prove2.me/submissions/8d40f515-2794-4036-8c57-2a7b7c501202

import Theorems.Thm_fta_winding_rootless_boundary_has_lift
import Theorems.Thm_fta_winding_homotopy_preserves_lift
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section
open Complex
open scoped Real unitInterval

private lemma ftaNorm_coe {z : ℂ} (hz : z ≠ 0) : (FtaNormalize z : ℂ) = z / (‖z‖ : ℂ) := by
  rw [FtaNormalize, dif_neg hz]

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
theorem solution (f : Polynomial ℂ) (R : ℝ)
    (hR : 0 < R) (hrootless : FtaClosedDiskRootless f R) :
    FtaHasLift (FtaBoundaryLoop f R) := by
  have hbp : Continuous (fun θ : FtaCircle => FtaBoundaryPoint R θ) := by
    unfold FtaBoundaryPoint
    exact continuous_const.mul
      (continuous_subtype_val.comp (AddCircle.homeomorphCircle').continuous)
  have hPnorm : ∀ θ : FtaCircle, ‖FtaBoundaryPoint R θ‖ = R := by
    intro θ
    rw [FtaBoundaryPoint, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
      Real.norm_of_nonneg hR.le]
  set inner : ↥unitInterval × FtaCircle → ℂ :=
    fun p => f.eval (((p.1 : ℝ) : ℂ) * FtaBoundaryPoint R p.2) with hinner
  have hcoeI : Continuous (fun p : ↥unitInterval × FtaCircle => (((p.1 : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have hinner_cont : Continuous inner :=
    f.continuous.comp (hcoeI.mul (hbp.comp continuous_snd))
  have hinner_ne : ∀ p : ↥unitInterval × FtaCircle, inner p ≠ 0 := by
    rintro ⟨t, θ⟩
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hzle : ‖((t : ℝ) : ℂ) * FtaBoundaryPoint R θ‖ ≤ R := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, hPnorm θ]
      exact mul_le_of_le_one_left hR.le ht1
    exact hrootless _ hzle
  set c₀ : Circle := FtaNormalize (f.eval 0) with hc0
  obtain ⟨r, hr⟩ : ∃ r : ℝ, Circle.exp r = c₀ := by
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (AddCircle.homeomorphCircle'.symm c₀)
    exact ⟨x, by rw [← AddCircle.homeomorphCircle'_apply_mk, hx, Homeomorph.apply_symm_apply]⟩
  have hlift : FtaHasLift (fun _ : FtaCircle => c₀) :=
    ⟨fun _ => r, continuous_const, fun _ => hr⟩
  have hhom : FtaCircleHomotopic (fun _ : FtaCircle => c₀) (FtaBoundaryLoop f R) := by
    refine ⟨⟨fun p => FtaNormalize (inner p), ftaNorm_continuous hinner_cont hinner_ne⟩, ?_, ?_⟩
    · intro θ
      simp only [ContinuousMap.coe_mk]
      have e0 : ((0 : ↥unitInterval) : ℝ) = 0 := by norm_num
      have : inner (0, θ) = f.eval 0 := by
        simp only [hinner, e0, Complex.ofReal_zero, zero_mul]
      rw [this]
    · intro θ
      simp only [ContinuousMap.coe_mk]
      have e1 : ((1 : ↥unitInterval) : ℝ) = 1 := by norm_num
      have : inner (1, θ) = f.eval (FtaBoundaryPoint R θ) := by
        simp only [hinner, e1, Complex.ofReal_one, one_mul]
      rw [this]; rfl
  exact fta_winding_homotopy_preserves_lift _ _ hhom hlift
