-- Prove2me | solution 1 for mme_cwSquare_canonical_singleton_postmap_eq_zero_of_fine_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T23:07:43.20037+00:00
-- url     : https://prove2.me/submissions/7b6d6a7b-bfed-4a05-ae7e-5b5f959f62b2

import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_blockTensor_zero_basis_supported_universe_polymorphic
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_dwz_basis_label_projection

open MME Module PiTensorProduct TensorProduct
open MME.DWZStep1Support

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

private theorem cwThree_basis_mem_grade
    {K : Type u} [Field K] (q : ℕ) (i : Fin 3)
    (a : Fin (q + 2)) :
    cwThreeCanonicalBasis K q i a ∈
      (cwThreeCanonicalGrading K q).classOf i
        (cwSquareCoordGrade q a) := by
  exact Submodule.subset_span ⟨a, rfl, rfl⟩

private theorem cwSquareCanonicalBasis_apply_tmul
    {K : Type u} [Field K] (q : ℕ) (i : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareCanonicalBasis K q i p =
      cwThreeCanonicalBasis K q i p.1 ⊗ₜ[K]
        cwThreeCanonicalBasis K q i p.2 := by
  fin_cases i <;>
    exact Module.Basis.tensorProduct_apply _ _ _ _

/-- Every canonical square-basis pair is homogeneous for its two fine split
grades. -/
theorem mme_cwSquareCanonicalBasis_mem_fineSplitGrade
    {K : Type u} [Field K] (q : ℕ) (i : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareCanonicalBasis K q i p ∈
      (cwSquareFineSplitGrading K q).classOf i
        (fineSplitGrade
          (cwSquareCoordGrade q p.1)
          (cwSquareCoordGrade q p.2)) := by
  let x : (cwThreeCanonicalGrading K q).classOf i
      (cwSquareCoordGrade q p.1) :=
    ⟨cwThreeCanonicalBasis K q i p.1,
      cwThree_basis_mem_grade q i p.1⟩
  let y : (cwThreeCanonicalGrading K q).classOf i
      (cwSquareCoordGrade q p.2) :=
    ⟨cwThreeCanonicalBasis K q i p.2,
      cwThree_basis_mem_grade q i p.2⟩
  have h := TensorObj.TypeGrading.classKronEmbed_mem
    (cwThreeCanonicalGrading K q) (cwThreeCanonicalGrading K q) i
      (cwSquareCoordGrade q p.1) (cwSquareCoordGrade q p.2)
      (x ⊗ₜ[K] y)
  rw [show TensorObj.TypeGrading.classKronEmbed
      (cwThreeCanonicalGrading K q) (cwThreeCanonicalGrading K q) i
      (cwSquareCoordGrade q p.1) (cwSquareCoordGrade q p.2)
        (x ⊗ₜ[K] y) = cwSquareCanonicalBasis K q i p by
    unfold TensorObj.TypeGrading.classKronEmbed
    change (x.1 ⊗ₜ[K] y.1) = cwSquareCanonicalBasis K q i p
    simp only [x, y]
    exact (cwSquareCanonicalBasis_apply_tmul q i p).symm] at h
  exact h

/-- A zero fine block kills the selected canonical square-basis singleton in
all three modes, even after arbitrary linear postprocessing. -/
theorem solution
    {K : Type u} [Field K] (q : ℕ)
    (selected : ∀ _ : Fin 3, Fin (q + 2) × Fin (q + 2))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) →ₗ[K] W i)
    (hzero : (cwSquareFineSplitGrading K q).blockTensor
      (fun i ↦ fineSplitGrade
        (cwSquareCoordGrade q (selected i).1)
        (cwSquareCoordGrade q (selected i).2)) = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (MME.DWZComponentRestriction.basisLabelProjection
            (cwSquareCanonicalBasis K q i) id {selected i}))
        (TensorObj.kron (CWObj K q) (CWObj K q)).t = 0 := by
  let maps : ∀ i : Fin 3,
      ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) →ₗ[K] W i :=
    fun i ↦ (post i).comp
      (MME.DWZComponentRestriction.basisLabelProjection
        (cwSquareCanonicalBasis K q i) id {selected i})
  let grade : ∀ _ : Fin 3,
      Fin (q + 2) × Fin (q + 2) → Fin (3 * 3) :=
    fun _ p ↦ fineSplitGrade
      (cwSquareCoordGrade q p.1) (cwSquareCoordGrade q p.2)
  have hhomogeneous : ∀ (i : Fin 3)
      (p : Fin (q + 2) × Fin (q + 2)),
      cwSquareCanonicalBasis K q i p ∈
        (cwSquareFineSplitGrading K q).classOf i (grade i p) := by
    intro i p
    exact mme_cwSquareCanonicalBasis_mem_fineSplitGrade q i p
  change PiTensorProduct.map maps
      (TensorObj.kron (CWObj K q) (CWObj K q)).t = 0
  refine mme_piTensorProduct_map_eq_zero_of_blockTensor_zero_basis_supported_universe_polymorphic
    (T := TensorObj.kron (CWObj K q) (CWObj K q))
    (Index := fun _ : Fin 3 ↦ Fin (q + 2) × Fin (q + 2))
    (W := W) (cwSquareFineSplitGrading K q)
    (fun i ↦ cwSquareCanonicalBasis K q i) grade hhomogeneous
    selected maps ?_ ?_
  · intro i p hp
    simp only [maps, LinearMap.comp_apply,
      MME.DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
      if_neg hp, map_zero]
  · simpa only [grade] using hzero
