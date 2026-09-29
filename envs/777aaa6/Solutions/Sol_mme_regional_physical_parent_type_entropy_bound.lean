-- Prove2me | solution 1 for mme_regional_physical_parent_type_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:06.92058+00:00
-- url     : https://prove2.me/submissions/e5809376-ba9e-44ea-9726-0735841dc300

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_regional_parent_count_structure
import Theorems.Thm_mme_regional_parent_mixture_cube
import Theorems.Thm_mme_regional_conditional_histogram_entropy_bound
import Theorems.Thm_mme_recursive_joint_parent_type_card
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Mathlib
open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem solution {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (hmass : ∀ r, ∑ c, m r c = n r) (mu : Cell half R parent → CompleteWord ell → ℕ)
    (i : Fin 3) (eps : ℝ) (heps : 0 ≤ eps)
    (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m)
    (f : Position n → CompleteWord ell) (hg : Graded htotal i a f)
    (ht : RegionRealization.parentTypical htotal n m mu eps f) :
    Real.exp (parentPotential htotal n m mu - coarsePotential m i -
      ((∑ r, n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord ell) eps) ≤
      (6 * (((∑ r, n r : ℕ) : ℝ) + 1)) ^
        (R * (half + 1) * Fintype.card (Fin 2 → CompleteWord ell)) *
        Nat.card {g : Position n → CompleteWord ell //
          ParentType (RecursiveXHash.block i a) (parentCounts (RecursiveXHash.block i a) f) g} := by
  classical
  let eta := parentCounts (RecursiveXHash.block i a) f
  let S := ∑ r, n r
  let z := entropyModulus (Fin 2 → CompleteWord ell) eps
  let b := 6 * ((S : ℝ) + 1)
  have hstruct := mme_regional_parent_count_structure htotal i a f hg
  have hamb : ∀ r, RecursiveThinSplit.HasMarginalCounts (a r) (m r) :=
    (Finset.mem_filter.mp ((mme_recursive_x_hash_family_counts half R parent n m).1 ha)).2
  have hrow r j : ∑ w, eta r j w = marginalCounts m i r j :=
    (hstruct r).1 j |>.trans (hamb r i j)
  have hnr (r : Fin R) : n r ≤ S :=
    Finset.single_le_sum (f := n) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let E (r : Fin R) := (n r : ℝ) * entropy (RegionRealization.parentMixture htotal n m mu r) -
    massEntropy (fun j ↦ (marginalCounts m i r j : ℝ)) - (n r : ℝ) * z
  have hr (r : Fin R) : Real.exp (E r) ≤
      b ^ ((half + 1) * Fintype.card (Fin 2 → CompleteWord ell)) * histogramNumber (eta r) := by
    have hh := mme_regional_conditional_histogram_entropy_bound (eta r) (n r)
      (hstruct r).2.2.1 (hstruct r).2.2.2
      (RegionRealization.parentMixture htotal n m mu r)
      (mme_regional_parent_mixture_cube htotal n m hmass mu r) eps heps
      (by intro w; simpa only [eta,(hstruct r).2.1 w,← Nat.card_eq_fintype_card] using (ht r w).le)
    simp_rw [hrow] at hh
    simp only [Fintype.card_fin] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply pow_le_pow_left₀ (by positivity)
    dsimp [b]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right (hnr r) 1) (by norm_num)
  have he : ∑ r, E r = parentPotential htotal n m mu - coarsePotential m i - (S : ℝ) * z := by
    simp only [E,parentPotential,coarsePotential,Finset.sum_sub_distrib,← Finset.sum_mul,S,Nat.cast_sum]
  change Real.exp (parentPotential htotal n m mu - coarsePotential m i - (S : ℝ) * z) ≤ _
  rw [← he,Real.exp_sum,mme_recursive_joint_parent_type_card,Nat.cast_prod]
  calc
    _ ≤ ∏ r, (b ^ ((half + 1) * Fintype.card (Fin 2 → CompleteWord ell)) *
        (histogramNumber (eta r) : ℝ)) :=
      Finset.prod_le_prod (fun r _ ↦ (Real.exp_pos _).le) (fun r _ ↦ hr r)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul]
      congr 1
      dsimp [b,S]
      congr 1
      ring
