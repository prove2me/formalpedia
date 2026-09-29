-- Prove2me | solution 1 for mme_entropy_penalty_upper_stability
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:49:22.99199+00:00
-- url     : https://prove2.me/submissions/2dc67dc1-e6c1-4418-9561-f19a1d878b97

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_regional_entropy_penalty_bound
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

private theorem entropy_continuous {C : Type*} [Fintype C] :
    Continuous (entropy (W := C)) := by
  unfold entropy
  exact continuous_finset_sum _ (fun c _ ↦ Real.continuous_negMulLog.comp (continuous_apply c))

private theorem stable_constraints {C A : Type*} [Fintype C] [Fintype A]
    (f : (C → ℝ) → (A → ℝ)) (hf : Continuous f) (alpha : C → ℝ) (U delta : ℝ)
    (hd : 0 < delta)
    (hU : ∀ rho : C → ℝ, (∀ c, 0 ≤ rho c) → (∑ c, rho c = 1) →
      f rho = f alpha → entropy rho ≤ U) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ beta rho : C → ℝ,
      (∀ c, |beta c - alpha c| ≤ eps) → (∀ c, 0 ≤ rho c) →
      (∑ c, rho c = 1) → f rho = f beta → entropy rho ≤ U + delta := by
  classical
  let box : Set (C → ℝ) := Set.pi Set.univ (fun _ ↦ Set.Icc 0 1)
  let bad : Set (C → ℝ) := box ∩ {rho | ∑ c, rho c = 1} ∩ {rho | U + delta ≤ entropy rho}
  have hb : IsCompact box := isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  have hc : IsCompact bad :=
    (hb.inter_right (isClosed_eq (continuous_finset_sum _ (fun c _ ↦ continuous_apply c))
      continuous_const)).inter_right (isClosed_le continuous_const entropy_continuous)
  have hnot : f alpha ∉ f '' bad := by
    rintro ⟨rho,hr,he⟩
    have hp : ∀ c, 0 ≤ rho c := fun c ↦ (hr.1.1 c (Set.mem_univ _)).1
    have hh := hU rho hp hr.1.2 he
    have hh' : U + delta ≤ entropy rho := hr.2
    linarith
  have ho : IsOpen (f ⁻¹' (f '' bad)ᶜ) := (hc.image hf).isClosed.isOpen_compl.preimage hf
  obtain ⟨e,he,hball⟩ := Metric.isOpen_iff.mp ho alpha hnot
  refine ⟨e / 2,half_pos he,?_⟩
  intro beta rho hclose hp hm hsame
  have hdist : dist beta alpha < e := by
    apply (dist_pi_lt_iff he).mpr
    intro c
    rw [Real.dist_eq]
    exact (hclose c).trans_lt (half_lt_self he)
  have havoid := hball hdist
  by_contra hlarge
  apply havoid
  refine ⟨rho,⟨⟨?_,hm⟩,le_of_not_ge hlarge⟩,hsame⟩
  intro c _
  refine ⟨hp c,?_⟩
  rw [← hm]
  exact Finset.single_le_sum (fun c _ ↦ hp c) (Finset.mem_univ c)

theorem solution {degree : ℕ} {bounds : Fin 3 → ℕ}
    (alpha : Split degree bounds → ℝ) (hpos : ∀ c, 0 ≤ alpha c)
    (hmass : ∑ c, alpha c = 1) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ beta : Split degree bounds → ℝ,
      (∀ c, 0 ≤ beta c) → (∑ c, beta c = 1) →
      (∀ c, |beta c - alpha c| ≤ eps) →
      Real.log 2 * entropyPenalty beta ≤ Real.log 2 * entropyPenalty alpha + delta := by
  classical
  let f : (Split degree bounds → ℝ) → (Fin 3 × Fin (degree+1) → ℝ) :=
    fun rho g ↦ mme_modern_marginal (fun c ↦ c.val g.1) rho g.2
  have hf : Continuous f := by
    apply continuous_pi
    intro g
    exact continuous_finset_sum _ (fun c _ ↦ continuous_apply c.val)
  let U := entropy alpha + Real.log 2 * entropyPenalty alpha
  have hU : ∀ rho : Split degree bounds → ℝ, (∀ c, 0 ≤ rho c) → (∑ c, rho c = 1) →
      f rho = f alpha → entropy rho ≤ U := by
    intro rho hp hm he
    apply (mme_regional_entropy_penalty_bound alpha hpos hmass).2 rho
    exact ⟨hp,hm,fun i j ↦ congrFun he (i,j)⟩
  obtain ⟨e1,he1,hstable⟩ := stable_constraints f hf alpha U (delta/2) (half_pos hdelta) hU
  obtain ⟨e2,he2,hent⟩ := Metric.continuousAt_iff.mp (entropy_continuous (C := Split degree bounds)).continuousAt
    (delta/2) (half_pos hdelta)
  refine ⟨min e1 (e2/2),lt_min he1 (half_pos he2),?_⟩
  intro beta hp hm hclose
  have hent' : |entropy beta - entropy alpha| < delta/2 := by
    apply hent
    apply (dist_pi_lt_iff he2).mpr
    intro c
    rw [Real.dist_eq]
    exact ((hclose c).trans (min_le_right _ _)).trans_lt (half_lt_self he2)
  have hbound : ∀ rho ∈ SameMarginalDistributions beta, entropy rho ≤ U + delta/2 := by
    intro rho hr
    apply hstable beta rho (fun c ↦ (hclose c).trans (min_le_left _ _)) hr.1 hr.2.1
    funext g
    exact hr.2.2 g.1 g.2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbits (rho : Split degree bounds → ℝ) :
      mme_modern_entropyBits rho = entropy rho / Real.log 2 := rfl
  have hsup : sSup (mme_modern_entropyBits '' SameMarginalDistributions beta) ≤
      (U + delta/2) / Real.log 2 := by
    have hself : beta ∈ SameMarginalDistributions beta := ⟨hp,hm,fun _ _ ↦ rfl⟩
    apply csSup_le ⟨mme_modern_entropyBits beta,Set.mem_image_of_mem _ hself⟩
    rintro z ⟨rho,hr,rfl⟩
    rw [hbits]
    exact div_le_div_of_nonneg_right (hbound rho hr) hl.le
  have hmul := (le_div_iff₀ hl).mp hsup
  have hnorm : Real.log 2 * mme_modern_entropyBits beta = entropy beta := by
    rw [hbits]
    field_simp
  unfold entropyPenalty
  dsimp [U] at hmul
  rw [mul_sub,mul_sub]
  change Real.log 2 * sSup (mme_modern_entropyBits '' SameMarginalDistributions beta) -
    Real.log 2 * mme_modern_entropyBits beta ≤ _
  rw [hnorm]
  have ha : Real.log 2 * mme_modern_entropyBits alpha = entropy alpha := by
    rw [hbits]
    field_simp
  rw [ha]
  unfold entropyPenalty at hmul
  linarith [(abs_lt.mp hent').1]
