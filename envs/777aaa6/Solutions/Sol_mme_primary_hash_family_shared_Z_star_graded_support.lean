-- Prove2me | solution 1 for mme_primary_hash_family_shared_Z_star_graded_support
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:55:11.034362+00:00
-- url     : https://prove2.me/submissions/e69a1011-c739-4292-be6b-ec830851bb55

import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_TypeGrading_kron

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

/-- A shared-Z star has no graded blocks outside its diagonal fiber addresses. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} (G : T.TypeGrading 3)
    {N L B A H : ℕ} (family : CWQ6PrimaryHashFamily N L B A H)
    (a : Fin A) (σ : Fin 3 → Fin (H + 1))
    (hσ : σ ∉ Finset.univ.image (cTensorOneHOneAddress H)) :
    (starGrading G family a).blockTensor σ = 0 := by
  classical
  change PiTensorProduct.map (fun i => (starGrading G family a).blockProj i (σ i))
    (∑ h, PiTensorProduct.map (componentInclusion G family a h)
      (componentObj G family a h).t) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro h _
  have hne : σ ≠ cTensorOneHOneAddress H h := by
    intro heq
    apply hσ
    exact Finset.mem_image.mpr ⟨h, Finset.mem_univ _, heq.symm⟩
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ cTensorOneHOneAddress H h i := by
    by_contra hn
    exact hne (funext fun i => by simpa using not_exists.mp hn i)
  erw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have hz (x : (componentObj G family a h).V i) :
      (starGrading G family a).blockProj i (σ i)
        (componentInclusion G family a h i x) = 0 :=
    TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _ _ hi _
      (component_inclusion_mem G family a h i x)
  induction (componentObj G family a h).t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      rw [map_smul, PiTensorProduct.map_tprod]
      have ht : (PiTensorProduct.tprod K) (fun j => ((starGrading G family a).blockProj j (σ j)).comp
          (componentInclusion G family a h j) (v j)) = 0 := by
        apply MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) i
        exact hz (v i)
      rw [ht, smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

#print axioms solution
