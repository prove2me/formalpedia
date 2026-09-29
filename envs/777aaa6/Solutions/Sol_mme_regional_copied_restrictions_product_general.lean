-- Prove2me | solution 1 for mme_regional_copied_restrictions_product_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T00:55:21.114651+00:00
-- url     : https://prove2.me/submissions/161ec313-906a-4663-af80-5c30b39bdee6

import Definitions.Def_mme_recursive_regional_CW_data
import Theorems.Thm_mme_recursive_regional_CW_plan_sound
import Theorems.Thm_mme_profiled_CW_region_product_restrict
import Theorems.Thm_mme_regional_copied_restrictions_product
import Theorems.Thm_mme_profiled_CW_mode_permutation_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Theorems.Thm_mme_basis_projected_type_cover_restrict
import Theorems.Thm_mme_type_cover_uniform_copy_extraction
import Theorems.Thm_mme_batched_restrictions_compose
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_CW_three_canonical_support
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Algebra.BigOperators.Fin

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.DWZStep1Support MME.CompleteSplit Module PiTensorProduct TensorProduct
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

universe u

private theorem product_sums' {K : Type u} [Field K] {k : ℕ}
    (S : Fin k → TensorObj K 3) (copies : Fin k → ℕ) :
    Isomorphic (kronFin k (fun j ↦ bigAdd (fun _ : Fin (copies j) ↦ S j)))
      (bigAdd (fun _ : Fin (∏ j, copies j) ↦ kronFin k S)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [mme_toQ_kronFin, TensorQ.toQ_bigAdd]
  simp_rw [TensorQ.toQ_bigAdd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod, mme_toQ_kronFin]

/-- Product of per-part copy extractions with arbitrary output tensors. -/
theorem solution {K : Type u} [Field K] {k : ℕ}
    (source : TensorObj K 3) (S U : Fin k → TensorObj K 3) (inputs outputs : Fin k → ℕ)
    (hgroup : TensorObj.Restrict (kronFin k S) source)
    (h : ∀ j, TensorObj.Restrict (bigAdd (fun _ : Fin (outputs j) ↦ U j))
      (bigAdd (fun _ : Fin (inputs j) ↦ S j))) :
    TensorObj.Restrict (bigAdd (fun _ : Fin (∏ j, outputs j) ↦ kronFin k U))
      (bigAdd (fun _ : Fin (∏ j, inputs j) ↦ source)) := by
  classical
  choose f hf using h
  have hk : TensorObj.Restrict (kronFin k (fun j ↦ bigAdd (fun _ : Fin (outputs j) ↦ U j)))
      (kronFin k (fun j ↦ bigAdd (fun _ : Fin (inputs j) ↦ S j))) :=
    ⟨kronFinFamilyModeMap k _ _ f, kronFinFamilyModeMap_preserves_tensor _ _ f hf⟩
  exact (product_sums' U outputs).2.trans (hk.trans ((product_sums' S inputs).1.trans
    (mme_bigAdd_mono_restrict (fun _ : Fin (∏ j, inputs j) ↦ hgroup))))
