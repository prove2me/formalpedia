-- Prove2me | solution 1 for mme_regional_physical_hash_load_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:18:50.215229+00:00
-- url     : https://prove2.me/submissions/741d24a3-0ff0-4740-a060-19d53c47ac6a

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_regional_target_marginals
import Theorems.Thm_mme_regional_target_entropy_bounds
import Theorems.Thm_mme_regional_target_fiber_entropy_bound
import Theorems.Thm_mme_regional_ambient_entropy_bound
import Theorems.Thm_mme_regional_coarse_entropy_bound
import Theorems.Thm_mme_regional_physical_parent_type_entropy_bound
import Theorems.Thm_mme_regional_entropy_uniform_modulus
import Theorems.Thm_mme_recursive_compatibility_entropy_bounds
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Mathlib
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000

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

theorem solution {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (ref : Address half R parent n) (href : ref ∈ RecursiveXHash.target m) :
    0 ≤ scaleExponent htotal n m mu eps ∧
    ∀ j : LoadIndex half R ell parent n,
      (loadNum htotal m d (fun i ↦ mu (yzMode i))
        (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps) j : ℝ) ≤
      loadFactor (half := half) (parent := parent) n d ell *
        Real.exp (scaleExponent htotal n m mu eps) * loadDen m j := by
  classical
  let A0 := jointPotential m
  let P := penaltyPotential n m
  let E := regionalRate htotal n m mu
  let loss := ((∑ r, n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord ell) eps
  let theta := scaleExponent htotal n m mu eps
  let PB := polynomialFactor n (R * (half + 1))
  let PD := polynomialFactor n (R * (half + 1) * Fintype.card (Fin 2 → CompleteWord ell))
  let CA := ambientFactor (half := half) (parent := parent) n
  have hm := (mme_regional_target_marginals m 0 ref href).1
  have hamb := mme_regional_ambient_entropy_bound n m hm
  have hPB : 0 ≤ PB := by dsimp [PB,polynomialFactor]; positivity
  have hPD : 0 ≤ PD := by dsimp [PD,polynomialFactor]; positivity
  have hCA : 0 ≤ CA := by dsimp [CA,ambientFactor]; positivity
  have hloss : 0 ≤ loss := mul_nonneg (Nat.cast_nonneg _)
    ((mme_regional_entropy_uniform_modulus (W := Fin 2 → CompleteWord ell)).1 eps heps)
  have hEX : E ≤ coarsePotential m 0 - P := min_le_left _ _
  have hEY (i : Fin 2) : E ≤ parentPotential htotal n m (mu (yzMode i)) -
      compatibilityPotential i (mu (yzMode i)) := by
    fin_cases i
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have htheta : 0 ≤ theta := by
    have hc := mme_regional_coarse_entropy_bound m 0
    change 0 ≤ A0 - E + loss
    dsimp [A0,P] at *
    linarith [hamb.1]
  refine ⟨htheta,?_⟩
  intro j
  rcases j with u | ⟨i,a,f⟩
  · have hblock := (mme_regional_target_entropy_bounds m 0 ref href).2.2.2
    have hden : Real.exp (coarsePotential m 0) ≤ PB * (loadDen (ell := ell) (n := n) m (Sum.inl u) : ℝ) := by
      apply hblock.trans
      apply mul_le_mul_of_nonneg_left _ hPB
      apply Nat.cast_le.mpr
      exact (Finset.card_le_card (Finset.image_subset_image
        (mme_recursive_x_hash_family_counts half R parent n m).1)).trans (le_max_right _ _)
    have ha : (8 * (RecursiveXHash.ambient (n := n) m).card : ℝ) ≤
        (8 * CA) * Real.exp (A0 + P) := by
      have hh := mul_le_mul_of_nonneg_left hamb.2 (by norm_num : (0 : ℝ) ≤ 8)
      simpa only [A0,P,CA,ambientFactor,mul_assoc] using hh
    have hraw := divide_exponent _ _ (8 * CA) PB (A0 + P) (coarsePotential m 0)
      (by positivity) ha hden
    have hex : A0 + P - coarsePotential m 0 ≤ theta := by
      change A0 + P - coarsePotential m 0 ≤ A0 - E + loss
      linarith
    change (↑(8 * (RecursiveXHash.ambient (n := n) m).card) : ℝ) ≤ _
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    apply hraw.trans
    have hc : 8 * CA * PB ≤ loadFactor (half := half) (parent := parent) n d ell := by
      change 8 * CA * PB ≤ 8 * CA * PB + 128 * (d : ℝ) * PB * PD
      exact le_add_of_nonneg_right (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul hc (Real.exp_le_exp.mpr hex) (Real.exp_pos _).le
      (by dsimp [loadFactor,polynomialFactor,ambientFactor]; positivity)
  · by_cases hkeep : a ∈ RecursiveXHash.target m ∧
        f ∈ unbrokenWords htotal (yzMode i) a (mu (yzMode i)) ∧
        parentTypical htotal n m (mu (yzMode i)) eps f
    · have hf := mme_regional_target_fiber_entropy_bound m (yzMode i) a hkeep.1
      have hcompat := (mme_recursive_compatibility_entropy_bounds
        (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) 1 (by omega)).1
      simp only [Nat.mul_one,Nat.cast_one,one_mul] at hcompat
      have hparent := mme_regional_physical_parent_type_entropy_bound htotal n m hm
        (mu (yzMode i)) (yzMode i) eps heps a hkeep.1 f
        (Finset.mem_filter.mp hkeep.2.1).2.1 hkeep.2.2
      let B := coarsePotential m (yzMode i)
      let H := parentPotential htotal n m (mu (yzMode i))
      let K := compatibilityPotential i (mu (yzMode i))
      have hn : ((128 * d * ((RecursiveXHash.target (n := n) m).filter (fun b ↦
          RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
          compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) : ℕ) : ℝ) ≤
          (128 * (d : ℝ) * PB) * Real.exp (A0 - B + K) := by
        simp only [Nat.cast_mul,Nat.cast_ofNat]
        calc
          _ ≤ (128 * (d : ℝ) * (PB * Real.exp (A0 - B))) * Real.exp K :=
            mul_le_mul (mul_le_mul_of_nonneg_left hf (by positivity)) hcompat
              (Nat.cast_nonneg _) (by positivity)
          _ = _ := by rw [Real.exp_add]; ring
      have hraw := divide_exponent _ (loadDen m (Sum.inr (i,a,f)) : ℝ)
        (128 * (d : ℝ) * PB) PD (A0 - B + K) (H - B - loss)
        (by positivity) hn hparent
      have hex : A0 - B + K - (H - B - loss) ≤ theta := by
        have h := hEY i
        change E ≤ H - K at h
        change _ ≤ A0 - E + loss
        linarith
      simp only [loadNum,if_pos hkeep]
      apply hraw.trans
      have hc : (128 * (d : ℝ) * PB) * PD ≤ loadFactor (half := half) (parent := parent) n d ell := by
        change 128 * (d : ℝ) * PB * PD ≤ 8 * CA * PB + 128 * (d : ℝ) * PB * PD
        exact le_add_of_nonneg_left (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul hc (Real.exp_le_exp.mpr hex) (Real.exp_pos _).le
        (by dsimp [loadFactor,polynomialFactor,ambientFactor]; positivity)
    · simp only [loadNum,if_neg hkeep,Nat.cast_zero]
      apply mul_nonneg _ (Nat.cast_nonneg _)
      apply mul_nonneg _ (Real.exp_pos _).le
      dsimp [loadFactor,polynomialFactor,ambientFactor]
      positivity
