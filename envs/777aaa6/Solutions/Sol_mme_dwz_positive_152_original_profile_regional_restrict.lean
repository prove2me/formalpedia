-- Prove2me | solution 1 for mme_dwz_positive_152_original_profile_regional_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T02:07:47.720986+00:00
-- url     : https://prove2.me/submissions/50870854-6866-4c40-98cc-d524f88eeb59

import Theorems.Thm_mme_dwz_prescribed_z_power_mixed_regional_restrict
import Definitions.Def_mme_dwz_positive_152_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
  MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent152
  Module BigOperators
open scoped Classical
universe u
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent152

theorem exact_weight_sum : ∑ r, regionalWeight r = 999999999999999 := by
  norm_num [regionalWeight, Fin.sum_univ_succ]

theorem exact_profile_mixture (a : Fin 5) :
    parentProfile.count a = ∑ r, (regionalProfile r).count a * regionalWeight r := by
  fin_cases a <;>
    norm_num [parentProfile, regionalProfile, region0, region1, region2,
      regionalWeight, Fin.sum_univ_succ]

theorem parent_profile_nontrivial :
    parentProfile.count 0 > 0 ∧ parentProfile.count 1 > 0 ∧ parentProfile.count 2 > 0 := by
  decide +kernel

end MME.DWZPositiveComponent152

theorem solution
    {K : Type u} [Field K] (q m : ℕ) :
    (∑ r, regionalWeight r = 999999999999999) ∧
    (∀ a : Fin 5, parentProfile.count a =
      ∑ r, (regionalProfile r).count a * regionalWeight r) ∧
    parentProfile.length m =
      ∑ r, (regionalProfile r).length (regionalWeight r * m) ∧
    TensorObj.Restrict
      (TensorObj.kronFin 3 (fun r ↦ prescribedZPower
        (cwFourthConstituent K q 1 5 2)
        (constituentBasis K q 1 5 2 2)
        (fun a : LiftedCoarseCoordinate.{u} q 2 ↦ cwSquarePairGrade q a.down.val.1)
        (regionalProfile r) (regionalWeight r * m)))
      (prescribedZPower
        (cwFourthConstituent K q 1 5 2)
        (constituentBasis K q 1 5 2 2)
        (fun a : LiftedCoarseCoordinate.{u} q 2 ↦ cwSquarePairGrade q a.down.val.1)
        parentProfile m) := by
  have hcounts (a : Fin 5) :
      parentProfile.count a * m =
        ∑ r, (regionalProfile r).count a * (regionalWeight r * m) := by
    rw [exact_profile_mixture, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ ↦ Nat.mul_assoc _ _ _)
  have hlength : parentProfile.length m =
      ∑ r, (regionalProfile r).length (regionalWeight r * m) := by
    calc
      parentProfile.length m = ∑ a, parentProfile.count a * m := by
        rw [← Finset.sum_mul, parentProfile.count_sum]
        rfl
      _ = ∑ a, ∑ r, (regionalProfile r).count a * (regionalWeight r * m) :=
        Finset.sum_congr rfl (fun a _ ↦ hcounts a)
      _ = ∑ r, ∑ a, (regionalProfile r).count a * (regionalWeight r * m) := Finset.sum_comm
      _ = _ := by simp only [← Finset.sum_mul, IntegerZSplitProfile.count_sum,
        IntegerZSplitProfile.length]
  refine ⟨exact_weight_sum, exact_profile_mixture, hlength, ?_⟩
  exact mme_dwz_prescribed_z_power_mixed_regional_restrict
    (cwFourthConstituent K q 1 5 2) (constituentBasis K q 1 5 2)
    (fun a : LiftedCoarseCoordinate.{u} q 2 ↦ cwSquarePairGrade q a.down.val.1)
    parentProfile m regionalProfile (fun r ↦ regionalWeight r * m) hlength hcounts