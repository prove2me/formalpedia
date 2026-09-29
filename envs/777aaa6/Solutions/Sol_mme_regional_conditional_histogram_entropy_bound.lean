-- Prove2me | solution 1 for mme_regional_conditional_histogram_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:02.865218+00:00
-- url     : https://prove2.me/submissions/5eca329c-5c0e-4aa7-aeb6-9aa104906ebf

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_regional_sparse_conditional_entropy
import Theorems.Thm_mme_regional_entropy_uniform_modulus
import Theorems.Thm_mme_regional_histogram_entropy_bounds
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1400000

private theorem nat_normalized {W : Type*} [Fintype W] (x : W → ℕ) :
    massEntropy (fun w ↦ (x w : ℝ)) =
      (∑ w, (x w : ℝ)) * entropy (fun w ↦ (x w : ℝ) / ∑ v, (x v : ℝ)) := by
  by_cases hz : ∑ w, (x w : ℝ) = 0
  · have hx : ∀ w, (x w : ℝ) = 0 := fun w ↦
      (Finset.sum_eq_zero_iff_of_nonneg (fun w _ ↦ Nat.cast_nonneg (x w))).mp hz w (Finset.mem_univ _)
    simp [hx,massEntropy,entropy]
  · exact (mme_regional_mass_entropy_algebra (C := Unit) (W := W)).2.1 _ hz

theorem solution {J W : Type*} [Fintype J] [Fintype W]
    (eta : J → W → ℕ) (n : ℕ) (hmass : ∑ j, ∑ w, eta j w = n)
    (hsparse : ∀ w j k, eta j w ≠ 0 → eta k w ≠ 0 → j = k)
    (p : W → ℝ) (hp : ∀ w, p w ∈ Set.Icc 0 1)
    (eps : ℝ) (heps : 0 ≤ eps)
    (htypical : ∀ w, |((∑ j, eta j w : ℕ) : ℝ) / n - p w| ≤ eps) :
    Real.exp ((n : ℝ) * entropy p - massEntropy (fun j ↦ ((∑ w, eta j w : ℕ) : ℝ)) -
      (n : ℝ) * entropyModulus W eps) ≤
      (6 * ((n : ℝ) + 1)) ^ (Fintype.card J * Fintype.card W) * histogramNumber eta := by
  classical
  let q : W → ℝ := fun w ↦ ((∑ j, eta j w : ℕ) : ℝ) / n
  have hcol : ∑ w, ∑ j, eta j w = n := by rw [Finset.sum_comm]; exact hmass
  have hq : ∀ w, q w ∈ Set.Icc 0 1 := by
    intro w
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · by_cases hn : n = 0
      · simp [q,hn]
      · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
        exact_mod_cast (show ∑ j, eta j w ≤ n by
          rw [← hcol]; exact Finset.single_le_sum (f := fun w ↦ ∑ j, eta j w)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ w))
  have he := (mme_regional_entropy_uniform_modulus (W := W)).2.1 eps q p hq hp htypical
  have hnorm : massEntropy (fun w ↦ ((∑ j, eta j w : ℕ) : ℝ)) = (n : ℝ) * entropy q := by
    rw [nat_normalized]
    simp only [← Nat.cast_sum,hcol]
    rfl
  have hchain := mme_regional_sparse_conditional_entropy (fun j w ↦ (eta j w : ℝ))
    (by intro w j k hj hk; apply hsparse w j k <;> exact fun h ↦ (by simp [h] at *))
  simp only [← Nat.cast_sum] at hchain
  rw [hnorm] at hchain
  have hsum : (n : ℝ) * entropy p - massEntropy (fun j ↦ ((∑ w, eta j w : ℕ) : ℝ)) -
      (n : ℝ) * entropyModulus W eps ≤ ∑ j, massEntropy (fun w ↦ (eta j w : ℝ)) := by
    rw [hchain]
    have hh := (abs_le.mp he).1
    have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n)
    linarith
  apply (Real.exp_le_exp.mpr hsum).trans
  exact (mme_regional_histogram_entropy_bounds eta n (fun j ↦ by
    rw [← hmass]; exact Finset.single_le_sum (f := fun j ↦ ∑ w, eta j w)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))).2
