-- Prove2me | solution 1 for mme_global_CW_hash_load_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:54:12.928106+00:00
-- url     : https://prove2.me/submissions/579d19bf-00d6-4596-a9d9-2568e647cecd

import Definitions.Def_mme_global_CW_entropy_data
import Theorems.Thm_mme_global_CW_word_histogram_entropy_bounds
import Theorems.Thm_mme_regional_target_marginals
import Theorems.Thm_mme_regional_target_entropy_bounds
import Theorems.Thm_mme_regional_target_fiber_entropy_bound
import Theorems.Thm_mme_regional_ambient_entropy_bound
import Theorems.Thm_mme_regional_coarse_entropy_bound
import Theorems.Thm_mme_recursive_compatibility_entropy_bounds
import Theorems.Thm_mme_recursive_x_hash_family_counts
open BigOperators MME MME.GlobalCW MME.RegionRate MME.RegionRealization MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

private theorem divide_exponent (x y u v a b : ℝ) (hu : 0 ≤ u)
    (hx : x ≤ u * Real.exp a) (hy : Real.exp b ≤ v * y) :
    x ≤ u * v * Real.exp (a - b) * y := by
  calc
    x ≤ u * Real.exp a := hx
    _ = (u * Real.exp (a - b)) * Real.exp b := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ (u * Real.exp (a - b)) * (v * y) :=
      mul_le_mul_of_nonneg_left hy (mul_nonneg hu (Real.exp_pos _).le)
    _ = _ := by ring

theorem solution {ell M : ℕ} (D : CountedStage ell M) :
    0 ≤ D.entropyExponent ∧ ∀ j : Fin 3,
      (D.num j : ℝ) ≤ D.entropyLoadFactor * Real.exp D.entropyExponent * D.den j := by
  classical
  let A := jointPotential D.m
  let P := penaltyPotential D.n D.m
  let E := D.entropyRate
  let theta := D.entropyExponent
  let PB := polynomialFactor D.n (D.R * (D.degree+1))
  let PD := polynomialFactor D.n (D.R * (D.degree+1) * Fintype.card (CompleteSplit.CompleteWord ell))
  let CA := ambientFactor (half := D.degree) (parent := D.bounds) D.n
  have hm := (mme_regional_target_marginals D.m 0 D.reference D.reference_target).1
  have hamb := mme_regional_ambient_entropy_bound D.n D.m hm
  have hPB : 0 ≤ PB := by dsimp [PB,polynomialFactor]; positivity
  have hPD : 0 ≤ PD := by dsimp [PD,polynomialFactor]; positivity
  have hCA : 0 ≤ CA := by dsimp [CA,ambientFactor]; positivity
  have hL : 0 ≤ D.entropyLoadFactor := by
    unfold CountedStage.entropyLoadFactor polynomialFactor ambientFactor
    positivity
  have hEX : E ≤ coarsePotential D.m 0 - P := min_le_left _ _
  have hEY (i : Fin 2) : E ≤ coarsePotential D.m (yzMode i) + D.wordPotential (yzMode i) -
      compatibilityPotential i (D.mu (yzMode i)) := by
    fin_cases i
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have htheta : 0 ≤ theta := by
    have hc := mme_regional_coarse_entropy_bound D.m 0
    change 0 ≤ A - E
    dsimp [A,P] at *
    linarith [hamb.1]
  have hx : (D.num 0 : ℝ) ≤ D.entropyLoadFactor * Real.exp theta * D.den 0 := by
    have hblock := (mme_regional_target_entropy_bounds D.m 0 D.reference D.reference_target).2.2.2
    have hden : Real.exp (coarsePotential D.m 0) ≤ PB * (D.den 0 : ℝ) := by
      apply hblock.trans
      apply mul_le_mul_of_nonneg_left _ hPB
      apply Nat.cast_le.mpr
      exact Finset.card_le_card (Finset.image_subset_image
        (mme_recursive_x_hash_family_counts D.degree D.R D.bounds D.n D.m).1)
    have ha : (8 * (RecursiveXHash.ambient (n := D.n) D.m).card : ℝ) ≤
        (8 * CA) * Real.exp (A + P) := by
      have hh := mul_le_mul_of_nonneg_left hamb.2 (by norm_num : (0 : ℝ) ≤ 8)
      simpa only [A,P,CA,ambientFactor,mul_assoc] using hh
    have hraw := divide_exponent _ _ (8 * CA) PB (A + P) (coarsePotential D.m 0)
      (by positivity) ha hden
    have hex : A + P - coarsePotential D.m 0 ≤ theta := by
      change _ ≤ A - E
      linarith
    change (↑(8 * (RecursiveXHash.ambient (n := D.n) D.m).card) : ℝ) ≤ _
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    apply hraw.trans
    have hc : 8 * CA * PB ≤ D.entropyLoadFactor := by
      change 8 * CA * PB ≤ 8 * CA * PB + 128 * (D.repairScale : ℝ) * PB * PD
      exact le_add_of_nonneg_right (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul hc (Real.exp_le_exp.mpr hex) (Real.exp_pos _).le hL
  have hf (i : Fin 3) : (D.fiberMax i : ℝ) ≤ PB * Real.exp (A - coarsePotential D.m i) := by
    obtain ⟨a,ha,hmax⟩ := Finset.exists_mem_eq_sup
      (s := RecursiveXHash.target (n := D.n) D.m)
      (f := fun a ↦ ((RecursiveXHash.target (n := D.n) D.m).filter
        (fun b ↦ RecursiveXHash.block i b = RecursiveXHash.block i a)).card)
      ⟨D.reference,D.reference_target⟩
    unfold CountedStage.fiberMax
    rw [hmax]
    exact mme_regional_target_fiber_entropy_bound D.m i a ha
  have hyz (i : Fin 2) :
      ((128 * D.repairScale * D.fiberMax (yzMode i) *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (D.mu (yzMode i)) : ℕ) : ℝ) ≤
      D.entropyLoadFactor * Real.exp theta * modeNumber (yzMode i) (D.mu (yzMode i)) := by
    have hcompat := (mme_recursive_compatibility_entropy_bounds
      (yzBoundary i) (modeGroup (yzMode i)) (D.mu (yzMode i)) 1 (by omega)).1
    simp only [Nat.mul_one,Nat.cast_one,one_mul] at hcompat
    have hword := (mme_global_CW_word_histogram_entropy_bounds D (yzMode i)).2
    let B := coarsePotential D.m (yzMode i)
    let H := D.wordPotential (yzMode i)
    let K := compatibilityPotential i (D.mu (yzMode i))
    have hn : ((128 * D.repairScale * D.fiberMax (yzMode i) *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (D.mu (yzMode i)) : ℕ) : ℝ) ≤
        (128 * (D.repairScale : ℝ) * PB) * Real.exp (A - B + K) := by
      simp only [Nat.cast_mul,Nat.cast_ofNat]
      calc
        _ ≤ (128 * (D.repairScale : ℝ) * (PB * Real.exp (A - B))) * Real.exp K :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hf (yzMode i)) (by positivity)) hcompat
            (Nat.cast_nonneg _) (by positivity)
        _ = _ := by rw [Real.exp_add]; ring
    have hraw := divide_exponent _ _ (128 * (D.repairScale : ℝ) * PB) PD
      (A - B + K) H (by positivity) hn hword
    have hex : A - B + K - H ≤ theta := by
      have h := hEY i
      change E ≤ B + H - K at h
      change _ ≤ A - E
      linarith
    apply hraw.trans
    have hc : 128 * (D.repairScale : ℝ) * PB * PD ≤ D.entropyLoadFactor := by
      change _ ≤ 8 * CA * PB + 128 * (D.repairScale : ℝ) * PB * PD
      exact le_add_of_nonneg_left (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul hc (Real.exp_le_exp.mpr hex) (Real.exp_pos _).le hL
  refine ⟨htheta,?_⟩
  intro j
  fin_cases j
  · exact hx
  · exact hyz 0
  · exact hyz 1
