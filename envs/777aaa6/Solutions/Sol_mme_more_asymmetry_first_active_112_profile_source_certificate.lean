-- Prove2me | solution 1 for mme_more_asymmetry_first_active_112_profile_source_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:32:01.969032+00:00
-- url     : https://prove2.me/submissions/cb98e8d4-9db6-4fac-a8a3-efb4e90b5a47

import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Theorems.Thm_mme_dwz_fourth_pair_factor_restrictions_to_coarse
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096

open BigOperators MME
open MME.MoreAsymmetryFirstSlice

universe u

private theorem probability_nonnegative (rotation mode : Fin 3) (word : Fin 2 → Fin 3) :
    0 ≤ probability rotation mode word := by
  unfold probability baseProbability
  split_ifs <;> norm_num [split0]

private theorem probability_sum (rotation mode : Fin 3) :
    (∑ word : Fin 2 → Fin 3, probability rotation mode word) = 1 := by
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp (probability rotation mode)]
  fin_cases rotation <;> fin_cases mode <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ,
      finTwoArrowEquiv, probability, baseProbability, split0, Fin.add_def]

theorem solution :
    (0 < split0 ∧ split0 < 1 / 2) ∧
    (0 < globalParentWeight ∧ 0 < parentRegionWeight ∧
      0 < firstSplitWeight ∧ 0 < fourthSplitWeight) ∧
    (firstPositiveParentPosition = 10 ∧ fourthShapes[10]? = some parentShape) ∧
    (firstChildOrder = [![0, 0, 4], ![1, 1, 2], ![0, 1, 3], ![1, 0, 3]]) ∧
    (∀ rotation mode : Fin 3,
      (∀ word : Fin 2 → Fin 3, 0 ≤ probability rotation mode word) ∧
      (∑ word : Fin 2 → Fin 3, probability rotation mode word) = 1 ∧
      (∀ word : Fin 2 → Fin 3,
        probability rotation mode word ≠ 0 ↔
          (word 0).val + (word 1).val = shape rotation mode)) ∧
    ((DWZSquare.shapeX publicPair.1).val + (DWZSquare.shapeX publicPair.2).val = 1 ∧
      (DWZSquare.shapeY publicPair.1).val + (DWZSquare.shapeY publicPair.2).val = 1 ∧
      (DWZSquare.shapeZ publicPair.1).val + (DWZSquare.shapeZ publicPair.2).val = 6) ∧
    (∃ beta : Fin 3 → Fin 3 → CompleteSplit.Profile 2,
      ∀ rotation mode word,
        (beta rotation mode).probability word = (probability rotation mode word : ℝ)) ∧
    (∀ (K : Type u) [Field K],
      TensorObj.Restrict
        (TensorObj.kron
          ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 0 4))
          ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 1 1 2)))
        ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor ![1, 1, 6])) := by
  refine ⟨by norm_num [split0],
    by norm_num [globalParentWeight, parentRegionWeight, firstSplitWeight, fourthSplitWeight],
    by decide, by decide, ?_, by decide, ?_, ?_⟩
  · intro rotation mode
    refine ⟨probability_nonnegative rotation mode, probability_sum rotation mode, ?_⟩
    intro word
    generalize h0 : word 0 = a
    generalize h1 : word 1 = b
    fin_cases rotation <;> fin_cases mode <;> fin_cases a <;> fin_cases b <;>
      norm_num [probability, baseProbability, shape, split0, h0, h1, Fin.add_def]
  · let beta (rotation mode : Fin 3) : CompleteSplit.Profile 2 := {
      level_pos := by decide
      probability word := (probability rotation mode word : ℝ)
      nonnegative word := by exact_mod_cast probability_nonnegative rotation mode word
      sum_eq_one := by exact_mod_cast probability_sum rotation mode }
    exact ⟨beta, fun _ _ _ ↦ rfl⟩
  · intro K _
    have hid (T : TensorObj K 3) : TensorObj.Restrict T T :=
      ⟨fun _ ↦ LinearMap.id, by rw [PiTensorProduct.map_id]; rfl⟩
    exact mme_dwz_fourth_pair_factor_restrictions_to_coarse 5 (0, 12) ![1, 1, 6]
      (by decide) (by decide) (by decide)
      (hid _) (hid _)

