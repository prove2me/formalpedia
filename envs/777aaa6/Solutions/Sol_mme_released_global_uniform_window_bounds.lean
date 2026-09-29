-- Prove2me | solution 1 for mme_released_global_uniform_window_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T11:30:59.931511+00:00
-- url     : https://prove2.me/submissions/9009cc82-8d82-4b4e-a328-fd0ef6627c12

import Definitions.Def_mme_released_global_frame_data
import Theorems.Thm_mme_released_global_profile_normalization
import Theorems.Thm_mme_global_CW_nearby_profile_rate_bound
import Theorems.Thm_mme_global_CW_counted_rate_normalization
import Theorems.Thm_mme_regional_mass_entropy_algebra
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

private theorem single_rate (p : EntropyProfile 8 1 (fun _ _ ↦ 8) Word)
    (b : ℝ) (hb : 0 ≤ b) : p.rate (fun _ ↦ b) = b * p.rate (fun _ ↦ 1) := by
  simp only [EntropyProfile.rate,Fin.sum_univ_one,one_mul]
  rw [mul_min_of_nonneg _ _ hb,mul_min_of_nonneg _ _ hb]

attribute [local irreducible] jointRows alpha atom rowCounts jointCounts coarseCounts wordCounts shapeEquiv

theorem solution (owner : Fin 6) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (k : ℕ) (hk : 0 < k) (a : Reference owner k)
      (d : ℕ) (hd : 1 < d) (mu : (frame owner k hk a).AdmissibleProfile),
      (∀ i, windowGood owner k eps i (mu.val i)) →
      (blocks k : ℝ)*((profile owner).rate (fun _ ↦ 1)-delta) ≤
        ((frame owner k hk a).stage mu d hd).entropyRate ∧
      ((frame owner k hk a).stage mu d hd).entropyExponent ≤
        (blocks k : ℝ)*(massEntropy ((profile owner).1 0) -
          (profile owner).rate (fun _ ↦ 1)+delta) := by
  have hn := mme_released_global_profile_normalization owner
  obtain ⟨eps,heps,hnear⟩ := mme_global_CW_nearby_profile_rate_bound
    (profile owner) hn.1 hn.2.1 delta hdelta
  refine ⟨eps,heps,?_⟩
  intro k hk a d hd mu hgood
  let D := (frame owner k hk a).stage mu d hd
  let q : EntropyProfile 8 1 (fun _ _ ↦ 8) Word :=
    ((profile owner).1, fun i c w ↦ (mu.val i c w : ℝ)/(blocks k : ℝ))
  have hb : (0 : ℝ) < blocks k := by
    have h : 0 < blocks k := by unfold blocks denominator; positivity
    exact_mod_cast h
  have hrate := hnear q hn.1 hn.2.1 (by intros; simpa [q] using heps.le)
    hgood (fun _ ↦ (blocks k : ℝ)) (fun _ ↦ hb.le)
  have hnorm : D.entropyRate = q.rate (fun _ ↦ (blocks k : ℝ)) := by
    apply mme_global_CW_counted_rate_normalization D q
    · exact hn.2.2.2.2.1 k
    · intro i c w
      change (mu.val i c w : ℝ) = (blocks k : ℝ)*((mu.val i c w : ℝ)/(blocks k : ℝ))
      field_simp
  have hE : (blocks k : ℝ)*((profile owner).rate (fun _ ↦ 1)-delta) ≤ D.entropyRate := by
    rw [hnorm]
    rw [single_rate _ _ hb.le,Fin.sum_univ_one] at hrate
    nlinarith
  have hJ : jointPotential D.m = (blocks k : ℝ)*massEntropy ((profile owner).1 0) := by
    change (∑ r : Fin 1, massEntropy (fun c ↦ (counts owner k r c : ℝ))) = _
    rw [Fin.sum_univ_one]
    simp_rw [hn.2.2.2.2.1 k 0]
    exact (mme_regional_mass_entropy_algebra (C := Unit)).1 _ _
  refine ⟨hE,?_⟩
  change jointPotential D.m-D.entropyRate ≤ _
  rw [hJ]
  nlinarith
