-- Prove2me | solution 1 for mme_global_CW_counted_rate_normalization
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:49:31.800393+00:00
-- url     : https://prove2.me/submissions/10b32849-86ee-45c3-bff6-5e3e126eebb5

import Definitions.Def_mme_global_CW_real_entropy_profiles
import Theorems.Thm_mme_regional_mass_entropy_algebra
open BigOperators MME MME.GlobalCW MME.RegionRate MME.RegionRealization MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

private theorem local_sum {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    (i : Fin 3) (v : Cell degree R bounds → ℝ) (r : Fin R) (j : Fin (degree+1)) :
    (∑ c, if modeGroup i c = (r,j) then v c else 0) =
      ∑ c : RecursiveThinSplit.Split degree (bounds r), if c.val i = j then v ⟨r,c⟩ else 0 := by
  classical
  unfold modeGroup
  rw [Fintype.sum_sigma]
  simp only [Prod.mk.injEq]
  rw [Finset.sum_eq_single r]
  · simp
  · intro r' _ hne
    simp [hne]
  · simp

private theorem local_interior {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    (i : Fin 2) (v : Cell degree R bounds → ℝ) (r : Fin R) (j : Fin (degree+1)) :
    (∑ c, if ¬ yzBoundary i c ∧ modeGroup (yzMode i) c = (r,j) then v c else 0) =
      ∑ c : RecursiveThinSplit.Split degree (bounds r),
        if ¬ yzBoundary i ⟨r,c⟩ ∧ c.val (yzMode i) = j then v ⟨r,c⟩ else 0 := by
  have he (c : Cell degree R bounds) :
      (if ¬ yzBoundary i c ∧ modeGroup (yzMode i) c = (r,j) then v c else 0) =
      (if modeGroup (yzMode i) c = (r,j) then (if ¬ yzBoundary i c then v c else 0) else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [local_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp_all

private theorem boundary_sum {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    (i : Fin 2) (v : Cell degree R bounds → ℝ) :
    (∑ c : {c : Cell degree R bounds // yzBoundary i c}, v c.val) =
      ∑ r, ∑ c : {c : RecursiveThinSplit.Split degree (bounds r) // yzBoundary i ⟨r,c⟩}, v ⟨r,c.val⟩ := by
  classical
  let e : {c : Cell degree R bounds // yzBoundary i c} ≃
      (r : Fin R) × {c : RecursiveThinSplit.Split degree (bounds r) // yzBoundary i ⟨r,c⟩} :=
    { toFun := fun c ↦ ⟨c.val.1,⟨c.val.2,c.property⟩⟩
      invFun := fun c ↦ ⟨⟨c.1,c.2.val⟩,c.2.property⟩
      left_inv := fun c ↦ by cases c; rfl
      right_inv := fun c ↦ by cases c; rfl }
  have h := Fintype.sum_equiv e (fun c ↦ v c.val) (fun c ↦ v ⟨c.1,c.2.val⟩) (fun c ↦ rfl)
  simpa only [Fintype.sum_sigma] using h

theorem solution {ell M : ℕ} (D : CountedStage ell M)
    (q : EntropyProfile D.degree D.R D.bounds (CompleteSplit.CompleteWord ell))
    (hm : ∀ r c, (D.m r c : ℝ) = (D.n r : ℝ) * q.1 r c)
    (hmu : ∀ i c w, (D.mu i c w : ℝ) = (D.n c.1 : ℝ) * q.2 i c w) :
    D.entropyRate = q.rate (fun r ↦ (D.n r : ℝ)) := by
  classical
  have hom (a : ℝ) (v : CompleteSplit.CompleteWord ell → ℝ) :
      massEntropy (fun w ↦ a * v w) = a * massEntropy v :=
    (mme_regional_mass_entropy_algebra (C := Unit)).1 a v
  have coarse (i : Fin 3) : coarsePotential D.m i = ∑ r, (D.n r : ℝ) * q.coarse i r := by
    unfold coarsePotential EntropyProfile.coarse
    apply Finset.sum_congr rfl
    intro r _
    have hmargin (j : Fin (D.degree+1)) : (marginalCounts D.m i r j : ℝ) =
        (D.n r : ℝ) * mme_modern_marginal (fun c ↦ c.val i) (q.1 r) j := by
      simp only [marginalCounts,mme_modern_marginal,Nat.cast_sum,hm,Finset.mul_sum]
    simp_rw [hmargin]
    exact (mme_regional_mass_entropy_algebra (C := Unit)).1 _ _
  have words (i : Fin 3) : D.wordPotential i = ∑ r, (D.n r : ℝ) * q.words i r := by
    unfold CountedStage.wordPotential
    have ha (r : Fin D.R) (j : Fin (D.degree+1)) (w : CompleteSplit.CompleteWord ell) :
        (aggregate i (D.mu i) r j w : ℝ) = (D.n r : ℝ) *
          ∑ c : RecursiveThinSplit.Split D.degree (D.bounds r),
            if c.val i = j then q.2 i ⟨r,c⟩ w else 0 := by
      simp only [aggregate,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
      rw [local_sum]
      simp only [hmu,Finset.mul_sum,mul_ite,mul_zero]
    simp_rw [ha,hom]
    rw [Fintype.sum_prod_type]
    simp only [EntropyProfile.words,Finset.mul_sum]
  have compat (i : Fin 2) : compatibilityPotential i (D.mu (yzMode i)) =
      ∑ r, (D.n r : ℝ) * q.compat i r := by
    unfold compatibilityPotential
    rw [(mme_regional_mass_entropy_algebra).2.2]
    rw [Fintype.sum_sum_type]
    simp only [partCount]
    have hi (r : Fin D.R) (j : Fin (D.degree+1)) (w : CompleteSplit.CompleteWord ell) :
        ((∑ c, if ¬ yzBoundary i c ∧ modeGroup (yzMode i) c = (r,j) then
          D.mu (yzMode i) c w else 0 : ℕ) : ℝ) = (D.n r : ℝ) *
          ∑ c : RecursiveThinSplit.Split D.degree (D.bounds r),
            if ¬ yzBoundary i ⟨r,c⟩ ∧ c.val (yzMode i) = j then q.2 (yzMode i) ⟨r,c⟩ w else 0 := by
      simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
      rw [local_interior]
      simp only [hmu,Finset.mul_sum,mul_ite,mul_zero]
    rw [boundary_sum i (fun c ↦ massEntropy (fun w ↦ (D.mu (yzMode i) c w : ℝ)))]
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    unfold EntropyProfile.compat
    rw [mul_add]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      simp_rw [hmu]
      exact hom _ _
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hom]
      congr 1
      funext w
      convert hi r j w using 1
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> rfl
  have penalty : penaltyPotential D.n D.m =
      ∑ r, (D.n r : ℝ) * (Real.log 2 * RecursiveThinSplit.entropyPenalty (q.1 r)) := by
    unfold penaltyPotential
    apply Finset.sum_congr rfl
    intro r _
    by_cases hz : D.n r = 0
    · simp [hz]
    · have hn : (D.n r : ℝ) ≠ 0 := by exact_mod_cast hz
      have he : (fun c ↦ (D.m r c : ℝ) / D.n r) = q.1 r := by
        funext c
        rw [hm]
        field_simp
      rw [he]
      ring
  have h0 : compatibilityPotential 0 (D.mu 1) = ∑ r, (D.n r : ℝ) * q.compat 0 r := by
    simpa [yzMode] using compat 0
  have h1 : compatibilityPotential 1 (D.mu 2) = ∑ r, (D.n r : ℝ) * q.compat 1 r := by
    simpa [yzMode] using compat 1
  unfold CountedStage.entropyRate EntropyProfile.rate
  rw [coarse,coarse,coarse,words,words,h0,h1,penalty]
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
