-- Prove2me | solution 1 for mme_primary_hash_family_shared_Z_star_graded_component
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:55:11.820095+00:00
-- url     : https://prove2.me/submissions/200444aa-f962-4671-afcf-7aadad97b2f3

import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_tensor_quotient

open MME Module PiTensorProduct CoupledCTensorPackaging
open scoped BigOperators
universe u
set_option autoImplicit false

private theorem star_basis_mem
    {K : Type u} [Field K] {T : TensorObj K 3} (G : T.TypeGrading 3)
    {N L B A H : ℕ} (family : CWQ6PrimaryHashFamily N L B A H)
    (a : Fin A) (i : Fin 3) (j : starBasisIndex G family a i) :
    starBasis G family a i j ∈ (starGrading G family a).classOf i
      (starBasisGrade G family a i j) := by
  exact Submodule.subset_span ⟨j, rfl, rfl⟩

private theorem component_inclusion_mem
    {K : Type u} [Field K] {T : TensorObj K 3} (G : T.TypeGrading 3)
    {N L B A H : ℕ} (family : CWQ6PrimaryHashFamily N L B A H)
    (a : Fin A) (h : Fin H) (i : Fin 3) (x : (componentObj G family a h).V i) :
    componentInclusion G family a h i x ∈ (starGrading G family a).classOf i
      (cTensorOneHOneAddress H h i) := by
  classical
  fin_cases i
  · rw [← (Module.finBasis K ((componentObj G family a h).V 0)).sum_repr x]
    erw [map_sum]
    apply Submodule.sum_mem
    intro j _
    erw [map_smul]
    apply Submodule.smul_mem
    have hm := star_basis_mem G family a 0 ⟨h, j⟩
    change (Pi.basis (fun k => Module.finBasis K ((componentObj G family a k).V 0)))
      ⟨h, j⟩ ∈ (starGrading G family a).classOf 0 h.castSucc at hm
    erw [Pi.basis_apply] at hm
    exact hm
  · rw [← (Module.finBasis K ((componentObj G family a h).V 1)).sum_repr x]
    erw [map_sum]
    apply Submodule.sum_mem
    intro j _
    erw [map_smul]
    apply Submodule.smul_mem
    have hm := star_basis_mem G family a 1 ⟨h, j⟩
    change (Pi.basis (fun k => Module.finBasis K ((componentObj G family a k).V 1)))
      ⟨h, j⟩ ∈ (starGrading G family a).classOf 1 h.castSucc at hm
    erw [Pi.basis_apply] at hm
    exact hm
  · let y := componentInclusion G family a h 2 x
    change y ∈ (starGrading G family a).classOf 2 (Fin.last H)
    rw [← (Module.finBasis K ((starObj G family a).V 2)).sum_repr y]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact star_basis_mem G family a 2 j

private noncomputable def componentRetraction
    {K : Type u} [Field K] {T : TensorObj K 3} (G : T.TypeGrading 3)
    {N L B A H : ℕ} (family : CWQ6PrimaryHashFamily N L B A H)
    (a : Fin A) (h : Fin H) : ∀ i : Fin 3,
      (starObj G family a).V i →ₗ[K] (componentObj G family a h).V i
  | 0 => LinearMap.proj h
  | 1 => LinearMap.proj h
  | 2 => (componentZEquiv G family a h).symm.toLinearMap

private theorem componentRetraction_inclusion
    {K : Type u} [Field K] {T : TensorObj K 3} (G : T.TypeGrading 3)
    {N L B A H : ℕ} (family : CWQ6PrimaryHashFamily N L B A H)
    (a : Fin A) (h : Fin H) (i : Fin 3) (x : (componentObj G family a h).V i) :
    componentRetraction G family a h i (componentInclusion G family a h i x) = x := by
  fin_cases i
  · change (Pi.single h x : ∀ k, (componentObj G family a k).V 0) h = x
    simp
  · change (Pi.single h x : ∀ k, (componentObj G family a k).V 1) h = x
    simp
  · exact (componentZEquiv G family a h).symm_apply_apply x

private theorem star_block_eq_component
    {K : Type u} [Field K] {T : TensorObj K 3} (G : T.TypeGrading 3)
    {N L B A H : ℕ} (family : CWQ6PrimaryHashFamily N L B A H)
    (a : Fin A) (h : Fin H) :
    (starGrading G family a).blockTensor (cTensorOneHOneAddress H h) =
      PiTensorProduct.map (fun i =>
        ((starGrading G family a).blockProj i (cTensorOneHOneAddress H h i)).comp
          (componentInclusion G family a h i)) (componentObj G family a h).t := by
  classical
  change PiTensorProduct.map _ (∑ k, PiTensorProduct.map
    (componentInclusion G family a k) (componentObj G family a k).t) = _
  rw [map_sum]
  rw [Finset.sum_eq_single h]
  · symm
    erw [PiTensorProduct.map_comp, LinearMap.comp_apply]
  · intro k _ hk
    have hz (x : (componentObj G family a k).V 0) :
        (starGrading G family a).blockProj 0 (cTensorOneHOneAddress H h 0)
          (componentInclusion G family a k 0 x) = 0 := by
      apply TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _
        (cTensorOneHOneAddress H k 0)
      · exact fun heq => hk (Fin.castSucc_injective H heq).symm
      · exact component_inclusion_mem G family a k 0 x
    erw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    induction (componentObj G family a k).t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
        rw [map_smul, PiTensorProduct.map_tprod]
        have ht : PiTensorProduct.tprod K (fun i =>
            ((starGrading G family a).blockProj i (cTensorOneHOneAddress H h i)).comp
              (componentInclusion G family a k i) (v i)) = 0 := by
          apply MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) 0
          exact hz (v 0)
        erw [ht, smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  · simp

/-- Each surviving graded block of a shared-Z star is isomorphic to its
original address component. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} (G : T.TypeGrading 3)
    {N L B A H : ℕ} (family : CWQ6PrimaryHashFamily N L B A H)
    (a : Fin A) (h : Fin H) :
    TensorObj.Isomorphic (componentObj G family a h)
      ((starGrading G family a).blockSubtensor (cTensorOneHOneAddress H h)) := by
  let F := fun i =>
    ((starGrading G family a).blockProj i (cTensorOneHOneAddress H h i)).comp
      (componentInclusion G family a h i)
  let R := fun i => (componentRetraction G family a h i).comp
    ((starGrading G family a).classOf i (cTensorOneHOneAddress H h i)).subtype
  have hRF : (fun i => (R i).comp (F i)) = fun i => LinearMap.id := by
    funext i
    apply LinearMap.ext
    intro x
    change componentRetraction G family a h i
      (((starGrading G family a).blockProj i (cTensorOneHOneAddress H h i)
        (componentInclusion G family a h i x) :
        (starGrading G family a).classOf i (cTensorOneHOneAddress H h i)) :
        (starObj G family a).V i) = x
    rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _
      (component_inclusion_mem G family a h i x)]
    exact componentRetraction_inclusion G family a h i x
  constructor
  · refine ⟨R, ?_⟩
    change PiTensorProduct.map R
      ((starGrading G family a).blockTensor (cTensorOneHOneAddress H h)) = _
    rw [star_block_eq_component]
    change PiTensorProduct.map R (PiTensorProduct.map F _) = _
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp, hRF, PiTensorProduct.map_id]
    rfl
  · exact ⟨F, (star_block_eq_component G family a h).symm⟩

#print axioms solution
