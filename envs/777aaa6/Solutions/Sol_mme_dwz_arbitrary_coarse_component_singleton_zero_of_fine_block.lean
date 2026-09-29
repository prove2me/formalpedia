-- Prove2me | solution 1 for mme_dwz_arbitrary_coarse_component_singleton_zero_of_fine_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:35:22.686214+00:00
-- url     : https://prove2.me/submissions/c9c2cfc0-552f-45ea-b022-89609c849967

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data
import Theorems.Thm_mme_cwSquare_canonical_singleton_postmap_eq_zero_of_fine_block
import Theorems.Thm_mme_dwz_coarseClassBasis_q6_val

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

private theorem arbitraryCoarseComponentModeBasis_coe
    {K : Type u} [Field K] (coarse : Fin 3 → Fin 5) (i : Fin 3)
    (p : DWZComponentRestriction.LiftedCoarsePair.{u} 6 (coarse i)) :
    (arbitraryCoarseComponentModeBasis K coarse i p).1 =
      cwSquareCanonicalBasis K 6 i p.down.1 := by
  have hr : arbitraryCoarseComponentModeBasis K coarse i p =
      DWZComponentRestriction.coarseClassBasis (K := K) 6 i
        (coarse i) p.down := by
    exact Module.Basis.reindex_apply
      (DWZComponentRestriction.coarseClassBasis (K := K) 6 i
        (coarse i)) Equiv.ulift.symm p
  rw [hr]
  exact mme_dwz_coarseClassBasis_q6_val K i (coarse i) p.down

private theorem arbitraryCoarse_selected_fullMap_basis_zero
    {K : Type u} [Field K] (coarse : Fin 3 → Fin 5)
    (selected : ∀ i,
      DWZComponentRestriction.LiftedCoarsePair.{u} 6 (coarse i))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      ((cwSquareCanonicalGrading K 6).blockSubtensor coarse).V i →ₗ[K]
        W i)
    (i : Fin 3) (p : Fin 8 × Fin 8)
    (hp : p ≠ (selected i).down.1) :
    post i
        (DWZComponentRestriction.basisLabelProjection
          (arbitraryCoarseComponentModeBasis K coarse i) id {selected i}
          ((cwSquareCanonicalGrading K 6).blockProj i (coarse i)
            (cwSquareCanonicalBasis K 6 i p))) = 0 := by
  by_cases hc : cwSquarePairGrade 6 p = coarse i
  · have hmem : cwSquareCanonicalBasis K 6 i p ∈
        (cwSquareCanonicalGrading K 6).classOf i (coarse i) := by
      exact Submodule.subset_span ⟨p, hc, rfl⟩
    let lifted : DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (coarse i) := ULift.up ⟨p, hc⟩
    have hvec :
        (⟨cwSquareCanonicalBasis K 6 i p, hmem⟩ :
          (cwSquareCanonicalGrading K 6).classOf i (coarse i)) =
        arbitraryCoarseComponentModeBasis K coarse i lifted := by
      apply Subtype.ext
      exact (arbitraryCoarseComponentModeBasis_coe
        (K := K) coarse i lifted).symm
    have hlifted : lifted ≠ selected i := by
      intro h
      apply hp
      exact congrArg (fun z ↦ z.down.1) h
    rw [TensorObj.TypeGrading.blockProj_apply_mem
      (cwSquareCanonicalGrading K 6) i (coarse i)
      (cwSquareCanonicalBasis K 6 i p) hmem, hvec]
    simp only [DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
      if_neg hlifted, map_zero]
  · have hmem : cwSquareCanonicalBasis K 6 i p ∈
        (cwSquareCanonicalGrading K 6).classOf i
          (cwSquarePairGrade 6 p) := by
      exact Submodule.subset_span ⟨p, rfl, rfl⟩
    rw [TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwSquareCanonicalGrading K 6) i (coarse i)
      (cwSquarePairGrade 6 p) (Ne.symm hc)
      (cwSquareCanonicalBasis K 6 i p) hmem]
    have hinner :
        DWZComponentRestriction.basisLabelProjection
          (arbitraryCoarseComponentModeBasis K coarse i) id {selected i} 0 =
        0 := LinearMap.map_zero _
    calc
      post i
          (DWZComponentRestriction.basisLabelProjection
            (arbitraryCoarseComponentModeBasis K coarse i) id
              {selected i} 0) = post i 0 :=
        congrArg (fun z ↦ post i z) hinner
      _ = 0 := LinearMap.map_zero _

private theorem arbitraryCoarse_selected_fullMap_factor
    {K : Type u} [Field K] (coarse : Fin 3 → Fin 5)
    (selected : ∀ i,
      DWZComponentRestriction.LiftedCoarsePair.{u} 6 (coarse i))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      ((cwSquareCanonicalGrading K 6).blockSubtensor coarse).V i →ₗ[K]
        W i)
    (i : Fin 3) :
    let componentMap := (post i).comp
      (DWZComponentRestriction.basisLabelProjection
        (arbitraryCoarseComponentModeBasis K coarse i) id {selected i})
    let fullMap := componentMap.comp
      ((cwSquareCanonicalGrading K 6).blockProj i (coarse i))
    fullMap.comp
        (DWZComponentRestriction.basisLabelProjection
          (cwSquareCanonicalBasis K 6 i) id {(selected i).down.1}) =
      fullMap := by
  dsimp only
  apply (cwSquareCanonicalBasis K 6 i).ext
  intro p
  by_cases hp : p = (selected i).down.1
  · subst p
    simp only [LinearMap.comp_apply,
      DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, id_eq, Finset.mem_singleton, if_true]
  · have hz := arbitraryCoarse_selected_fullMap_basis_zero
      coarse selected post i p hp
    have hs :
        DWZComponentRestriction.basisLabelProjection
          (cwSquareCanonicalBasis K 6 i) id {(selected i).down.1}
          (cwSquareCanonicalBasis K 6 i p) = 0 := by
      unfold DWZComponentRestriction.basisLabelProjection
      rw [Module.Basis.constr_basis]
      simp only [id_eq, Finset.mem_singleton, if_neg hp]
    rw [LinearMap.comp_apply, hs]
    exact (LinearMap.map_zero _).trans hz.symm

theorem solution
    {K : Type u} [Field K] (coarse : Fin 3 → Fin 5)
    (selected : ∀ i,
      DWZComponentRestriction.LiftedCoarsePair.{u} 6 (coarse i))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      ((cwSquareCanonicalGrading K 6).blockSubtensor coarse).V i →ₗ[K]
        W i)
    (hzero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ fineSplitGrade
        (selected i).leftGrade (selected i).rightGrade) = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (DWZComponentRestriction.basisLabelProjection
            (arbitraryCoarseComponentModeBasis K coarse i) id {selected i}))
        ((cwSquareCanonicalGrading K 6).blockSubtensor coarse).t = 0 := by
  let actual : ∀ _ : Fin 3, Fin 8 × Fin 8 :=
    fun i ↦ (selected i).down.1
  let localMaps : ∀ i,
      ((cwSquareCanonicalGrading K 6).blockSubtensor coarse).V i →ₗ[K]
        W i := fun i ↦ (post i).comp
      (DWZComponentRestriction.basisLabelProjection
        (arbitraryCoarseComponentModeBasis K coarse i) id {selected i})
  let blockMaps : ∀ i,
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i) →ₗ[K]
        ((cwSquareCanonicalGrading K 6).blockSubtensor coarse).V i :=
    fun i ↦ (cwSquareCanonicalGrading K 6).blockProj i (coarse i)
  let fullMaps : ∀ i,
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).V i) →ₗ[K] W i :=
    fun i ↦ (localMaps i).comp (blockMaps i)
  have hfine : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ fineSplitGrade
        (cwSquareCoordGrade 6 (actual i).1)
        (cwSquareCoordGrade 6 (actual i).2)) = 0 := by
    simpa only [actual,
      DWZComponentRestriction.LiftedCoarsePair.leftGrade,
      DWZComponentRestriction.LiftedCoarsePair.rightGrade,
      DWZComponentRestriction.CoarsePair.leftGrade,
      DWZComponentRestriction.CoarsePair.rightGrade] using hzero
  have hcw := mme_cwSquare_canonical_singleton_postmap_eq_zero_of_fine_block
    (K := K) 6 actual fullMaps hfine
  have hfamilies :
      (fun i ↦ (fullMaps i).comp
        (DWZComponentRestriction.basisLabelProjection
          (cwSquareCanonicalBasis K 6 i) id {actual i})) = fullMaps := by
    funext i
    simpa only [fullMaps, localMaps, blockMaps, actual] using
      arbitraryCoarse_selected_fullMap_factor coarse selected post i
  rw [hfamilies] at hcw
  change PiTensorProduct.map localMaps
      (PiTensorProduct.map blockMaps
        (TensorObj.kron (CWObj K 6) (CWObj K 6)).t) = 0
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  exact hcw
