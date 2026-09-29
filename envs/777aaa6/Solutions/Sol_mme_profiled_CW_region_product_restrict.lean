-- Prove2me | solution 1 for mme_profiled_CW_region_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:14:26.781853+00:00
-- url     : https://prove2.me/submissions/a69054af-5ad8-4917-8e99-03fd267eb26b

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes

open BigOperators MME MME.TensorObj MME.ProfiledCW Module PiTensorProduct
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
universe u

theorem solution {K : Type u} [Field K] {N parts : ℕ} (P : Predicate N)
    (size : Fin parts → ℕ) (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
    (Q : ∀ j, Predicate (size j))
    (inside : ∀ i x, (∀ j, Q j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x) :
    Restrict (kronFin parts (fun j ↦ tensor K (Q j))) (tensor K P) := by
  classical
  let R := fun j ↦ raw K (size j)
  let S := fun j ↦ tensor K (Q j)
  let G := fun j ↦ (R j).basisAllAllowedGrading (canonical K (size j))
    (fun i x ↦ Q j i (fine x))
  let proj := fun j i ↦ (G j).blockProj i 0
  obtain ⟨phi, ht, hb⟩ := mme_kronPow_fiber_grouping_preserves_tensor_and_basis
    (CWObj K 5) (fun i ↦ (MME.DWZStep1Support.cwThreeCanonicalBasis K 5 i).reindex Equiv.ulift.symm)
    size positions.symm
  change PiTensorProduct.map (fun i ↦ (phi i).toLinearMap) (raw K N).t =
    (kronFin parts R).t at ht
  have hB (i : Fin 3) (x : Coordinate.{u} N) :
      phi i (canonical K N i x) =
        kronFinModePiBasis parts R i (fun j ↦ canonical K (size j) i)
          (fun j r ↦ x (positions ⟨j,r⟩)) := hb i x
  let F := fun i ↦ (kronFinFamilyModeMap parts R S proj i).comp (phi i).toLinearMap
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes (raw K N)
    (kronFin parts S) (canonical K N) (fun i x ↦ P i (fine x)) F
  · change PiTensorProduct.map (fun i ↦
      (kronFinFamilyModeMap parts R S proj i).comp (phi i).toLinearMap) (raw K N).t = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    exact (congrArg (PiTensorProduct.map (kronFinFamilyModeMap parts R S proj)) ht).trans
      (kronFinFamilyModeMap_preserves_tensor R S proj (fun _ ↦ rfl))
  · intro i x hx
    change kronFinFamilyModeMap parts R S proj i (phi i (canonical K N i x)) = 0
    rw [hB]
    apply kronFinFamilyModeMap_basis_eq_zero_of_exists R S i
      (fun j ↦ canonical K (size j) i) proj
    have hbad : ¬ ∀ j, Q j i (fun r ↦ fine x (positions ⟨j,r⟩)) :=
      fun h ↦ hx (inside i (fine x) h)
    obtain ⟨j,hj⟩ := not_forall.mp hbad
    refine ⟨j, ?_⟩
    apply TensorObj.TypeGrading.blockProj_apply_mem_ne (G j) i 0 1 (by decide)
    exact Submodule.subset_span ⟨(fun r ↦ x (positions ⟨j,r⟩)), if_neg hj, rfl⟩
