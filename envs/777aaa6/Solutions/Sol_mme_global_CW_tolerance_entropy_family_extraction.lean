-- Prove2me | solution 1 for mme_global_CW_tolerance_entropy_family_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T09:03:34.973395+00:00
-- url     : https://prove2.me/submissions/ec8da48b-280b-4a77-9f82-92ca749a0c03

import Definitions.Def_mme_global_CW_real_entropy_profiles
import Definitions.Def_mme_global_CW_joint_start_data
import Theorems.Thm_mme_global_CW_nearby_profile_rate_bound
import Theorems.Thm_mme_global_CW_counted_rate_normalization
import Theorems.Thm_mme_global_CW_uniform_entropy_family_extraction
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
universe u

theorem solution {K : Type u} [Field K] {M ell types : ℕ} (T : Predicate M)
    (steps : Fin types → CountedStage ell M)
    (p : ∀ j, EntropyProfile (steps j).degree (steps j).R (steps j).bounds (CompleteSplit.CompleteWord ell))
    (hp : ∀ j r c, 0 ≤ (p j).1 r c) (hmass : ∀ j r, ∑ c, (p j).1 r c = 1)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ∀ j, EntropyProfile (steps j).degree (steps j).R (steps j).bounds (CompleteSplit.CompleteWord ell),
      (∀ j r c, 0 ≤ (q j).1 r c) → (∀ j r, ∑ c, (q j).1 r c = 1) →
      (∀ j r c, ((steps j).m r c : ℝ) = ((steps j).n r : ℝ) * (q j).1 r c) →
      (∀ j i c w, ((steps j).mu i c w : ℝ) = ((steps j).n c.1 : ℝ) * (q j).2 i c w) →
      (∀ j r c, |(q j).1 r c - (p j).1 r c| ≤ eps) →
      (∀ j i c w, |(q j).2 i c w - (p j).2 i c w| ≤ eps) →
      ∀ rate E S J P F h : ℝ, 0 ≤ rate →
      rate ≤ (E - delta * S) - Real.log P - Real.log (64 * F) -
        4 * Real.sqrt (Real.log F + J - (E - delta * S)) - h * Real.log 8 →
      (∀ j, E ≤ (p j).rate (fun r ↦ ((steps j).n r : ℝ))) →
      (∀ j, (∑ r, ((steps j).n r : ℝ)) ≤ S) →
      (∀ j, jointPotential (steps j).m ≤ J) →
      (∀ j, polynomialFactor (steps j).n
        (Fintype.card (Cell (steps j).degree (steps j).R (steps j).bounds)) ≤ P) →
      (∀ j, (steps j).entropyScaleFactor ≤ F) →
      (∀ j, ((steps j).repairExponent : ℝ) ≤ h) →
      (∀ j i x, (steps j).output i x → T i x) →
      (∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i)) →
      ∃ D : GlobalCW.Part M ell T, D.inputs = types ∧ D.rate = rate ∧
        Restrict (bigAdd (fun _ : Fin ⌈Real.exp rate⌉₊ ↦ tensor K T))
          (bigAdd (fun _ : Fin types ↦ tensor K (fun _ (_ : FineWord M) ↦ True))) := by
  classical
  choose es hes hs using (fun j ↦ mme_global_CW_nearby_profile_rate_bound
    (p j) (hp j) (hmass j) delta hdelta)
  have huniform : ∃ eps : ℝ, 0 < eps ∧ ∀ j, eps ≤ es j := by
    by_cases hz : types = 0
    · subst types
      exact ⟨1,by norm_num,fun j ↦ Fin.elim0 j⟩
    · haveI : Nonempty (Fin types) := ⟨⟨0,Nat.pos_of_ne_zero hz⟩⟩
      refine ⟨Finset.univ.inf' Finset.univ_nonempty es,?_,?_⟩
      · exact (Finset.lt_inf'_iff _).mpr (fun j _ ↦ hes j)
      · intro j
        exact Finset.inf'_le es (Finset.mem_univ j)
  obtain ⟨eps,heps,hle⟩ := huniform
  refine ⟨eps,heps,?_⟩
  intro q hqp hqm hcounts hwords hqa hqw rate E S J P F h hrate hbudget hE hS hJ hP hF hh inside cover
  apply mme_global_CW_uniform_entropy_family_extraction T steps rate (E - delta * S)
    J P F h hrate hbudget _ hJ hP hF hh inside cover
  intro j
  rw [mme_global_CW_counted_rate_normalization (steps j) (q j) (hcounts j) (hwords j)]
  have hbound := hs j (q j) (hqp j) (hqm j)
    (fun r c ↦ (hqa j r c).trans (hle j))
    (fun i c w ↦ (hqw j i c w).trans (hle j))
    (fun r ↦ ((steps j).n r : ℝ)) (fun r ↦ Nat.cast_nonneg _)
  have hloss := mul_le_mul_of_nonneg_left (hS j) hdelta.le
  linarith [hE j]
