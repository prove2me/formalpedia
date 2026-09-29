-- Prove2me | solution 1 for mme_regional_physical_entropy_selected_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T00:19:54.990858+00:00
-- url     : https://prove2.me/submissions/f84dbfc0-5660-4f5b-8a70-580f05c043d9

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_regional_physical_hash_load_entropy_bounds
import Theorems.Thm_mme_common_hash_scale_real_upper_bound
import Theorems.Thm_mme_regional_target_entropy_bounds
import Theorems.Thm_mme_entropy_retention_lower_bound
import Mathlib
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

/-! Entropy bounds for the physical hash construction, independent of an IntegerStep. -/

private theorem mme_regional_physical_common_scale_entropy_bound {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (ref : Address half R parent n) (href : ref ∈ RecursiveXHash.target m) :
    0 ≤ scaleExponent htotal n m mu eps ∧
    (commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i))
        (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m) : ℝ) ≤
      scaleFactor (half := half) (parent := parent) n d ell *
        Real.exp (scaleExponent htotal n m mu eps) := by
  have h := mme_regional_physical_hash_load_entropy_bounds htotal n m mu d eps heps ref href
  let theta := scaleExponent htotal n m mu eps
  let L := loadFactor (half := half) (parent := parent) n d ell
  have hL : 0 ≤ L := by dsimp [L, loadFactor, polynomialFactor, ambientFactor]; positivity
  have he : 1 ≤ Real.exp theta := Real.one_le_exp_iff.mpr h.1
  have hs := mme_common_hash_scale_real_upper_bound half
    (loadNum htotal m d (fun i ↦ mu (yzMode i))
      (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m)
    (L * Real.exp theta) (mul_nonneg hL (Real.exp_pos _).le) h.2
  refine ⟨h.1, hs.trans ?_⟩
  change (half : ℝ) + 2 + L * Real.exp theta ≤ ((half : ℝ) + 2 + L) * Real.exp theta
  have hh := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ (half : ℝ) + 2 by positivity)
  nlinarith

theorem solution {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (ref : Address half R parent n) (href : ref ∈ RecursiveXHash.target m) :
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i))
        (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m)
    let factor := scaleFactor (half := half) (parent := parent) n d ell
    let theta := scaleExponent htotal n m mu eps
    Real.exp (regionalRate htotal n m mu - ((∑ r, n r : ℕ) : ℝ) *
        entropyModulus (Fin 2 → CompleteWord ell) eps -
        4 * Real.sqrt (Real.log factor + theta)) /
      (32 * polynomialFactor n (Fintype.card (Cell half R parent)) * factor) ≤
    ((RecursiveXHash.target (n := n) m).card : ℝ) *
      Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) := by
  dsimp only
  have hs := mme_regional_physical_common_scale_entropy_bound htotal n m mu d eps heps ref href
  have ht := (mme_regional_target_entropy_bounds m 0 ref href).2.1
  have hQ : 0 < commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i))
        (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m) := by
    unfold commonScale
    exact (Nat.succ_pos half).trans_le (le_max_left _ _)
  have hp : 0 < polynomialFactor n (Fintype.card (Cell half R parent)) := by
    unfold polynomialFactor
    positivity
  have hf : 0 < scaleFactor (half := half) (parent := parent) n d ell := by
    unfold scaleFactor loadFactor polynomialFactor ambientFactor
    positivity
  have h := mme_entropy_retention_lower_bound
    ((RecursiveXHash.target (n := n) m).card : ℝ) (commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i))
        (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m) : ℝ)
    (jointPotential m) (scaleFactor (half := half) (parent := parent) n d ell)
    (scaleExponent htotal n m mu eps)
    (polynomialFactor n (Fintype.card (Cell half R parent)))
    (Nat.cast_nonneg _) (by exact_mod_cast hQ) hf hp ht hs.2
  have he : jointPotential m - scaleExponent htotal n m mu eps =
      regionalRate htotal n m mu - ((∑ r, n r : ℕ) : ℝ) *
        entropyModulus (Fin 2 → CompleteWord ell) eps := by
    unfold scaleExponent
    ring
  rw [he] at h
  exact h


#print axioms solution
