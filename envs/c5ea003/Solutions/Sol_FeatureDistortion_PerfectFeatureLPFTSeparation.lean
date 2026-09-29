-- Prove2me | solution 1 for FeatureDistortion.PerfectFeatureLPFTSeparation
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-27T17:20:21.66415+00:00
-- url     : https://prove2.me/submissions/ef833321-3388-4dec-bbe6-b6de8cde4fe4

import Definitions.Def_FeatureDistortion_Model
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Theorems.Thm_FeatureDistortion_BalancednessInvariant
import Theorems.Thm_FeatureDistortion_FrozenOrthogonalFeatures
import Theorems.Thm_FeatureDistortion_GaussianHeadMisalignment
import Theorems.Thm_FeatureDistortion_GradientFlowWellPosed
import Theorems.Thm_FeatureDistortion_LPFTStationary
import Theorems.Thm_FeatureDistortion_OODRiskIdentity
import Theorems.Thm_FeatureDistortion_PerfectFeatureLinearProbing

section RootGeometry
/-! Euclidean identities for the perfect-feature model, following Kumar et al.,
Appendix A.7, Proposition A.20, PDF pp. 45--46. -/

noncomputable section
namespace FeatureDistortion.UploadProof

lemma initialFeatures_adjoint {n d k : ℕ} (P : Problem n d k) (v : Vec k) :
    (initialFeatures P).adjoint v = P.optimalFeatures.adjoint (P.rotation.symm v) := by
  simp only [initialFeatures, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  change P.optimalFeatures.adjoint ((P.rotation : Vec k →L[ℝ] Vec k).adjoint v) = _
  rw [P.rotation.adjoint_eq_symm]
  rfl

lemma weights_aligned {n d k : ℕ} (P : Problem n d k) :
    weights (initialFeatures P) (alignedHead P) = targetWeights P := by
  simp [weights, initialFeatures_adjoint, alignedHead, targetWeights]

lemma alignedHead_ne_zero {n d k : ℕ} (P : Problem n d k) (h : Admissible P) :
    alignedHead P ≠ 0 := by
  simpa [alignedHead] using h.2.2.2.2.1

lemma mem_rowSpace_orthogonal_iff {n d : ℕ} (X : Vec d →L[ℝ] Vec n) (x : Vec d) :
    x ∈ (rowSpace X)ᗮ ↔ X x = 0 := by
  change x ∈ X.adjoint.rangeᗮ ↔ _
  rw [ContinuousLinearMap.orthogonal_range]
  simp

lemma visible_data_injective {n d k : ℕ} (X : Vec d →L[ℝ] Vec n) (B : Features d k)
    (h : VisibleOn B (rowSpace X)) : Function.Injective (X.comp B.adjoint) := by
  intro a b hab
  apply h
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub]
  apply (Submodule.starProjection_apply_eq_zero_iff _).2
  rw [mem_rowSpace_orthogonal_iff]
  simpa [map_sub, sub_eq_zero] using hab

lemma residual_eq_initial_map_sub {n d k : ℕ} (P : Problem n d k) (v : Vec k) :
    residual P.data (labels P) v (initialFeatures P) =
      P.data ((initialFeatures P).adjoint (v - alignedHead P)) := by
  simp [residual, labels, map_sub, ← weights_aligned P, weights]

lemma trainingLoss_eq_zero_iff {n d k : ℕ} (P : Problem n d k) (h : Admissible P)
    (v : Vec k) : trainingLoss P.data (labels P) v (initialFeatures P) = 0 ↔
      v = alignedHead P := by
  rw [trainingLoss, sq_eq_zero_iff, norm_eq_zero, residual_eq_initial_map_sub]
  have hi := visible_data_injective P.data (initialFeatures P) h.2.2.2.2.2.1
  change (P.data.comp (initialFeatures P).adjoint) (v - alignedHead P) = 0 ↔ _
  rw [map_eq_zero_iff _ hi, sub_eq_zero]

end FeatureDistortion.UploadProof

end -- original EOF-open anonymous section
end RootGeometry

section RootObstruction
/-! The qualitative obstruction behind Proposition 3.7 (Kumar et al., PDF p. 10;
Appendix A.7, PDF pp. 46--47). Frozen off-training-span features identify the head;
balancedness then forces one of the two exceptional Gaussian alignments. -/

noncomputable section
namespace FeatureDistortion.UploadProof

lemma head_eq_of_frozen_and_weights_eq {d k : ℕ} (S : Submodule ℝ (Vec d))
    (B₀ B : Features d k) (v u : Vec k) (hvis : VisibleOn B₀ S)
    (hfrozen : ∀ x ∈ S, B x = B₀ x) (hw : weights B v = weights B₀ u) : v = u := by
  apply hvis
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub]
  apply (Submodule.starProjection_apply_eq_zero_iff _).2
  intro x hx
  rw [map_sub, inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  rw [← hfrozen x hx, ← ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ x (weights B v) - inner ℝ (B x) u = 0
  rw [hw, hfrozen x hx]
  simp only [weights, ContinuousLinearMap.adjoint_inner_right, sub_self]

lemma alignment_zero_of_frozen_balance_weights {d k : ℕ} (S : Submodule ℝ (Vec d))
    (B₀ B : Features d k) (v₀ v u : Vec k) (hvis : VisibleOn B₀ S)
    (hfrozen : ∀ x ∈ S, B x = B₀ x)
    (hbalance : balance v B = balance v₀ B₀)
    (hw : weights B v = weights B₀ u) : alignmentError v₀ u = 0 := by
  have hv : v = u := head_eq_of_frozen_and_weights_eq S B₀ B v u hvis hfrozen hw
  subst v
  have hquad : inner ℝ u (B (B.adjoint u)) = inner ℝ u (B₀ (B₀.adjoint u)) := by
    calc
      _ = inner ℝ (B.adjoint u) (B.adjoint u) :=
        (B.adjoint_inner_left (B.adjoint u) u).symm
      _ = inner ℝ (B₀.adjoint u) (B₀.adjoint u) := congrArg (fun z ↦ inner ℝ z z) hw
      _ = _ := B₀.adjoint_inner_left (B₀.adjoint u) u
  have he := congrArg (fun T : Vec k →L[ℝ] Vec k ↦ inner ℝ u (T u)) hbalance
  simp only [balance, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, InnerProductSpace.rankOne_apply, real_inner_smul_right] at he
  rw [hquad, real_inner_comm u v₀] at he
  unfold alignmentError
  apply abs_eq_zero.mpr
  rw [real_inner_comm u v₀]
  nlinarith

end FeatureDistortion.UploadProof

end -- original EOF-open anonymous section
end RootObstruction

section RootSeparationCore
/-! The strict OOD-loss branch of Kumar et al., Proposition 3.7, PDF p. 10,
equation (3.10), using the qualitative alignment obstruction. -/

noncomputable section
open MeasureTheory
namespace FeatureDistortion.UploadProof

lemma fineTuning_ood_pos_of_misalignment {n d k : ℕ} (P : Problem n d k) (D : OODLaw d)
    (hP : Admissible P) (v₀ : Vec k) (ha : 0 < alignmentError v₀ (alignedHead P))
    (γ : Trajectory d k)
    (hγ : IsFineTuningFlow P.data (labels P) v₀ (initialFeatures P) γ)
    (t : ℝ) (ht : 0 ≤ t) :
    0 < oodLoss D (targetWeights P) (γ.head t) (γ.features t) := by
  apply (OODRiskIdentity d k D (targetWeights P) (γ.head t) (γ.features t)).2.2.mpr
  intro hw
  have hf := FrozenOrthogonalFeatures n d k P.data (labels P) v₀ (initialFeatures P) γ hγ t ht
  have hb := BalancednessInvariant n d k P.data (labels P) v₀ (initialFeatures P) γ hγ t ht
  have hz := alignment_zero_of_frozen_balance_weights (rowSpace P.data)ᗮ
    (initialFeatures P) (γ.features t) v₀ (γ.head t) (alignedHead P)
    hP.2.2.2.2.2.2 hf hb (hw.trans (weights_aligned P).symm)
  exact (ne_of_gt ha) hz

lemma ae_fineTuning_ood_pos {n d k : ℕ} (P : Problem n d k) (D : OODLaw d)
    (hP : Admissible P) (σ : ℝ) (hσ : 0 < σ) :
    ∀ᵐ v₀ ∂gaussianHead k σ, ∀ γ : Trajectory d k,
      IsFineTuningFlow P.data (labels P) v₀ (initialFeatures P) γ →
      ∀ t : ℝ, 0 ≤ t →
        0 < oodLoss D (targetWeights P) (γ.head t) (γ.features t) := by
  filter_upwards [GaussianHeadMisalignment k (alignedHead P) σ (alignedHead_ne_zero P hP) hσ]
    with v₀ hv₀
  exact fun γ hγ t ht ↦ fineTuning_ood_pos_of_misalignment P D hP v₀ hv₀ γ hγ t ht

end FeatureDistortion.UploadProof

end -- original EOF-open anonymous section
end RootSeparationCore

open MeasureTheory Filter
open scoped Topology

open FeatureDistortion
theorem solution :
  ∀ (n d k : ℕ) (P : Problem n d k) (D : OODLaw d), Admissible P →
    ∀ σ : ℝ, 0 < σ →
      (∀ v₀ : Vec k, ∃ γ : Trajectory d k,
        IsFineTuningFlow P.data (labels P) v₀ (initialFeatures P) γ) ∧
      (∀ v₀ : Vec k,
        (∃ v : ℝ → Vec k, IsLinearProbingFlow P.data (labels P) v₀ (initialFeatures P) v) ∧
        ∀ v : ℝ → Vec k,
          IsLinearProbingFlow P.data (labels P) v₀ (initialFeatures P) v →
          Tendsto v atTop (𝓝 (alignedHead P))) ∧
      (∀ γ : Trajectory d k,
        IsFineTuningFlow P.data (labels P) (alignedHead P) (initialFeatures P) γ →
        ∀ t : ℝ, 0 ≤ t →
          oodLoss D (targetWeights P) (γ.head t) (γ.features t) = 0) ∧
      (∀ᵐ v₀ ∂gaussianHead k σ, ∀ γ : Trajectory d k,
        IsFineTuningFlow P.data (labels P) v₀ (initialFeatures P) γ →
        ∀ t : ℝ, 0 ≤ t →
          0 < oodLoss D (targetWeights P) (γ.head t) (γ.features t)) := by
  intro n d k P D hP σ hσ
  refine ⟨?_, ?_, ?_, FeatureDistortion.UploadProof.ae_fineTuning_ood_pos P D hP σ hσ⟩
  · intro v₀
    exact (GradientFlowWellPosed n d k P.data (labels P) v₀ (initialFeatures P)).1
  · intro v₀
    exact ⟨(GradientFlowWellPosed n d k P.data (labels P) v₀ (initialFeatures P)).2.2,
      (PerfectFeatureLinearProbing n d k P hP).2 v₀⟩
  · intro γ hγ t ht
    obtain ⟨hv, hB⟩ := LPFTStationary n d k P hP γ hγ t ht
    rw [hv, hB]
    exact (OODRiskIdentity d k D (targetWeights P) (alignedHead P) (initialFeatures P)).2.1.mpr
      (FeatureDistortion.UploadProof.weights_aligned P)

