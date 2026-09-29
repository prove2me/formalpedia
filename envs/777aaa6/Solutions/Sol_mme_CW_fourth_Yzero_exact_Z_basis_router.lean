-- Prove2me | solution 1 for mme_CW_fourth_Yzero_exact_Z_basis_router
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T19:01:22.622316+00:00
-- url     : https://prove2.me/submissions/0e460a23-d0d5-4e0f-8f41-96ceb2325e60

import Theorems.Thm_mme_CW_fourth_Xzero_exact_Z_basis_router
import Mathlib.Tactic
import Definitions.Def_mme_stothers_oriented_cyclic_classes
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_TypeGrading_permutation

open MME PiTensorProduct TensorProduct Module BigOperators

universe u

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace MME.StothersFourth.NumericM5

private theorem piMap_map_apply_fin3
    {K : Type u} [Field K]
    {V W U : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (f : ∀ i, V i →ₗ[K] W i) (g : ∀ i, W i →ₗ[K] U i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map g (PiTensorProduct.map f x) =
      PiTensorProduct.map (fun i ↦ (g i).comp (f i)) x := by
  exact (LinearMap.congr_fun
    (PiTensorProduct.map_comp (f := f) (g := g)) x).symm

private noncomputable def cwSwapToBase
    (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3,
      CWSpace K q (swapFirstTwoPerm.symm i) →ₗ[K] CWSpace K q i :=
  fun ⟨i, hi⟩ ↦ by
    match i, hi with
    | 0, _ =>
        change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K)
        exact LinearMap.id
    | 1, _ =>
        change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K)
        exact LinearMap.id
    | 2, _ =>
        change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K)
        exact LinearMap.id
    | i + 3, h => exact absurd h (by omega)

private noncomputable def cwBaseToSwap
    (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3,
      CWSpace K q i →ₗ[K] CWSpace K q (swapFirstTwoPerm.symm i) :=
  fun ⟨i, hi⟩ ↦ by
    match i, hi with
    | 0, _ =>
        change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K)
        exact LinearMap.id
    | 1, _ =>
        change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K)
        exact LinearMap.id
    | 2, _ =>
        change (Fin (q + 2) → K) →ₗ[K] (Fin (q + 2) → K)
        exact LinearMap.id
    | i + 3, h => exact absurd h (by omega)

private theorem cwSwapToBase_monom
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    PiTensorProduct.map (cwSwapToBase K q)
      ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
        (CWMonom K q a b c)) = CWMonom K q b a c := by
  unfold CWMonom
  rw [PiTensorProduct.reindex_tprod]
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem cwSwapToBase_tensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwSwapToBase K q)
      ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
        (CWTensor K q)) = CWTensor K q := by
  unfold CWTensor
  simp only [map_add, map_sum, cwSwapToBase_monom]
  let O : Fin (q + 2) := ⟨0, by omega⟩
  have hsum :
      (∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        CWMonom K q M O M + CWMonom K q O M M +
          CWMonom K q M M O) =
      ∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        CWMonom K q O M M + CWMonom K q M O M +
          CWMonom K q M M O := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp
    abel
  rw [hsum]
  abel

private noncomputable def cwSquareSwapToBase
    (K : Type u) [Field K] (q : ℕ) : ∀ i : Fin 3,
    ((TensorObj.kron (CWObj K q) (CWObj K q)).V
      (swapFirstTwoPerm.symm i)) →ₗ[K]
    ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) :=
  fun i ↦ TensorProduct.map
    (cwSwapToBase K q i) (cwSwapToBase K q i)

private noncomputable def cwSquareBaseToSwap
    (K : Type u) [Field K] (q : ℕ) : ∀ i : Fin 3,
    ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) →ₗ[K]
    ((TensorObj.kron (CWObj K q) (CWObj K q)).V
      (swapFirstTwoPerm.symm i)) :=
  fun i ↦ TensorProduct.map
    (cwBaseToSwap K q i) (cwBaseToSwap K q i)

private theorem cwSquareSwapToBase_tensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwSquareSwapToBase K q)
      ((PiTensorProduct.reindex K
        (TensorObj.kron (CWObj K q) (CWObj K q)).V
        swapFirstTwoPerm)
        (TensorObj.kron (CWObj K q) (CWObj K q)).t) =
      (TensorObj.kron (CWObj K q) (CWObj K q)).t := by
  change PiTensorProduct.map (cwSquareSwapToBase K q)
      ((PiTensorProduct.reindex K
        (fun i ↦ CWSpace K q i ⊗[K] CWSpace K q i)
        swapFirstTwoPerm)
        (interchange (CWTensor K q) (CWTensor K q))) =
      interchange (CWTensor K q) (CWTensor K q)
  rw [reindex_interchange]
  change PiTensorProduct.map
      (fun i ↦ TensorProduct.map
        (cwSwapToBase K q i) (cwSwapToBase K q i))
      (interchange
        ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
          (CWTensor K q))
        ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
          (CWTensor K q))) = _
  rw [TensorObj.TypeGrading.kronMap_interchange,
    cwSwapToBase_tensor]

private noncomputable def cwFourthSwapToBase
    (K : Type u) [Field K] (q : ℕ) : ∀ i : Fin 3,
    (cwFourthObj K q).V (swapFirstTwoPerm.symm i) →ₗ[K]
      (cwFourthObj K q).V i :=
  fun i ↦ TensorProduct.map
    (cwSquareSwapToBase K q i) (cwSquareSwapToBase K q i)

private noncomputable def cwFourthBaseToSwap
    (K : Type u) [Field K] (q : ℕ) : ∀ i : Fin 3,
    (cwFourthObj K q).V i →ₗ[K]
      (cwFourthObj K q).V (swapFirstTwoPerm.symm i) :=
  fun i ↦ TensorProduct.map
    (cwSquareBaseToSwap K q i) (cwSquareBaseToSwap K q i)

private theorem cwFourthSwapToBase_tensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwFourthSwapToBase K q)
      ((PiTensorProduct.reindex K (cwFourthObj K q).V
        swapFirstTwoPerm) (cwFourthObj K q).t) =
      (cwFourthObj K q).t := by
  change PiTensorProduct.map (cwFourthSwapToBase K q)
      ((PiTensorProduct.reindex K
        (fun i ↦
          (TensorObj.kron (CWObj K q) (CWObj K q)).V i ⊗[K]
          (TensorObj.kron (CWObj K q) (CWObj K q)).V i)
        swapFirstTwoPerm)
        (interchange
          (TensorObj.kron (CWObj K q) (CWObj K q)).t
          (TensorObj.kron (CWObj K q) (CWObj K q)).t)) =
      interchange
        (TensorObj.kron (CWObj K q) (CWObj K q)).t
        (TensorObj.kron (CWObj K q) (CWObj K q)).t
  rw [reindex_interchange]
  change PiTensorProduct.map
      (fun i ↦ TensorProduct.map
        (cwSquareSwapToBase K q i) (cwSquareSwapToBase K q i))
      (interchange
        ((PiTensorProduct.reindex K
          (TensorObj.kron (CWObj K q) (CWObj K q)).V
          swapFirstTwoPerm)
          (TensorObj.kron (CWObj K q) (CWObj K q)).t)
        ((PiTensorProduct.reindex K
          (TensorObj.kron (CWObj K q) (CWObj K q)).V
          swapFirstTwoPerm)
          (TensorObj.kron (CWObj K q) (CWObj K q)).t)) = _
  rw [TensorObj.TypeGrading.kronMap_interchange,
    cwSquareSwapToBase_tensor]

private theorem cwSquareSwapToBase_basis
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareSwapToBase K q i
        (cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i) p) =
      cwSquareCanonicalBasis K q i p := by
  rcases p with ⟨a, b⟩
  fin_cases i <;>
    simp [swapFirstTwoPerm, cwSquareSwapToBase,
      cwSwapToBase, cwSquareCanonicalBasis] <;>
    exact LinearMap.congr_fun
      (TensorProduct.map_id (R := K)
        (M := Fin (q + 2) → K) (N := Fin (q + 2) → K)) _

private theorem cwSquareBaseToSwap_basis
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareBaseToSwap K q i (cwSquareCanonicalBasis K q i p) =
      cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i) p := by
  rcases p with ⟨a, b⟩
  fin_cases i <;>
    simp [swapFirstTwoPerm, cwSquareBaseToSwap,
      cwBaseToSwap, cwSquareCanonicalBasis] <;>
    exact LinearMap.congr_fun
      (TensorProduct.map_id (R := K)
        (M := Fin (q + 2) → K) (N := Fin (q + 2) → K)) _

private theorem cwFourthSwapToBase_basis
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3)
    (p :
      (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    cwFourthSwapToBase K q i
        (cwFourthCanonicalBasis K q (swapFirstTwoPerm.symm i) p) =
      cwFourthCanonicalBasis K q i p := by
  rcases p with ⟨p, r⟩
  change TensorProduct.map
      (cwSquareSwapToBase K q i) (cwSquareSwapToBase K q i)
      ((Module.Basis.tensorProduct
        (cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i))
        (cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i))) (p, r)) = _
  rw [Module.Basis.tensorProduct_apply, TensorProduct.map_tmul,
    cwSquareSwapToBase_basis, cwSquareSwapToBase_basis]
  change
    (cwSquareCanonicalBasis K q i) p ⊗ₜ[K]
        (cwSquareCanonicalBasis K q i) r =
      (Module.Basis.tensorProduct
        (cwSquareCanonicalBasis K q i)
        (cwSquareCanonicalBasis K q i)) (p, r)
  rw [Module.Basis.tensorProduct_apply]

private theorem cwFourthBaseToSwap_basis
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3)
    (p :
      (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    cwFourthBaseToSwap K q i
        (cwFourthCanonicalBasis K q i p) =
      cwFourthCanonicalBasis K q (swapFirstTwoPerm.symm i) p := by
  rcases p with ⟨p, r⟩
  change TensorProduct.map
      (cwSquareBaseToSwap K q i) (cwSquareBaseToSwap K q i)
      ((Module.Basis.tensorProduct
        (cwSquareCanonicalBasis K q i)
        (cwSquareCanonicalBasis K q i)) (p, r)) = _
  rw [Module.Basis.tensorProduct_apply, TensorProduct.map_tmul,
    cwSquareBaseToSwap_basis, cwSquareBaseToSwap_basis]
  change
    (cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i)) p ⊗ₜ[K]
        (cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i)) r =
      (Module.Basis.tensorProduct
        (cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i))
        (cwSquareCanonicalBasis K q (swapFirstTwoPerm.symm i))) (p, r)
  rw [Module.Basis.tensorProduct_apply]

private theorem cwFourthSwapToBase_mem_grade
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (a : Fin 9)
    (x : (cwFourthObj K q).V (swapFirstTwoPerm.symm i))
    (hx : x ∈ (cwFourthCanonicalGrading K q).classOf
      (swapFirstTwoPerm.symm i) a) :
    cwFourthSwapToBase K q i x ∈
      (cwFourthCanonicalGrading K q).classOf i a := by
  change x ∈ cwBasisGrade
      (cwFourthCanonicalBasis K q (swapFirstTwoPerm.symm i))
      (cwFourthPairGrade q) a at hx
  change cwFourthSwapToBase K q i x ∈ cwBasisGrade
      (cwFourthCanonicalBasis K q i) (cwFourthPairGrade q) a
  unfold cwBasisGrade at hx ⊢
  refine Submodule.span_induction
    (p := fun y _ ↦ cwFourthSwapToBase K q i y ∈
      Submodule.span K
        (cwFourthCanonicalBasis K q i ''
          {p | cwFourthPairGrade q p = a}))
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    rw [cwFourthSwapToBase_basis]
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  · simp
  · intro y z hy hz hy' hz'
    simpa using Submodule.add_mem _ hy' hz'
  · intro c y hy hy'
    simpa using Submodule.smul_mem _ c hy'

private theorem cwFourthBaseToSwap_mem_grade
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (a : Fin 9)
    (x : (cwFourthObj K q).V i)
    (hx : x ∈ (cwFourthCanonicalGrading K q).classOf i a) :
    cwFourthBaseToSwap K q i x ∈
      (cwFourthCanonicalGrading K q).classOf
        (swapFirstTwoPerm.symm i) a := by
  change x ∈ cwBasisGrade
      (cwFourthCanonicalBasis K q i) (cwFourthPairGrade q) a at hx
  change cwFourthBaseToSwap K q i x ∈ cwBasisGrade
      (cwFourthCanonicalBasis K q (swapFirstTwoPerm.symm i))
      (cwFourthPairGrade q) a
  unfold cwBasisGrade at hx ⊢
  refine Submodule.span_induction
    (p := fun y _ ↦ cwFourthBaseToSwap K q i y ∈
      Submodule.span K
        (cwFourthCanonicalBasis K q (swapFirstTwoPerm.symm i) ''
          {p | cwFourthPairGrade q p = a}))
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    rw [cwFourthBaseToSwap_basis]
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  · simp
  · intro y z hy hz hy' hz'
    simpa using Submodule.add_mem _ hy' hz'
  · intro c y hy hy'
    simpa using Submodule.smul_mem _ c hy'

private theorem cwFourthBaseToSwap_comp_swapToBase
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) :
    (cwFourthBaseToSwap K q i).comp (cwFourthSwapToBase K q i) =
      LinearMap.id := by
  let b := cwFourthCanonicalBasis K q (swapFirstTwoPerm.symm i)
  refine b.ext ?_
  intro p
  change cwFourthBaseToSwap K q i
      (cwFourthSwapToBase K q i (b p)) = b p
  rw [cwFourthSwapToBase_basis, cwFourthBaseToSwap_basis]

private noncomputable def fourthBlockSwapToBase
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9) : ∀ i : Fin 3,
    (cwFourthCanonicalGrading K q).classOf
        (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i)) →ₗ[K]
      (cwFourthCanonicalGrading K q).classOf i
        (fixedModeRelabel swapFirstTwoPerm ρ i) :=
  fun i ↦ LinearMap.codRestrict _
    ((cwFourthSwapToBase K q i).comp
      ((cwFourthCanonicalGrading K q).classOf
        (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i))).subtype)
    (fun x ↦ by
      change cwFourthSwapToBase K q i x.1 ∈
        (cwFourthCanonicalGrading K q).classOf i
          (fixedModeRelabel swapFirstTwoPerm ρ i)
      simpa [fixedModeRelabel] using
        (cwFourthSwapToBase_mem_grade K q i
          (ρ (swapFirstTwoPerm.symm i)) x.1 x.2))

private noncomputable def fourthBlockBaseToSwap
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9) : ∀ i : Fin 3,
    (cwFourthCanonicalGrading K q).classOf i
        (fixedModeRelabel swapFirstTwoPerm ρ i) →ₗ[K]
      (cwFourthCanonicalGrading K q).classOf
        (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i)) :=
  fun i ↦ LinearMap.codRestrict _
    ((cwFourthBaseToSwap K q i).comp
      ((cwFourthCanonicalGrading K q).classOf i
        (fixedModeRelabel swapFirstTwoPerm ρ i)).subtype)
    (fun x ↦ by
      apply cwFourthBaseToSwap_mem_grade K q i
        (ρ (swapFirstTwoPerm.symm i)) x.1
      exact x.2)

private theorem fourthBlockSwapToBase_blockProj
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9)
    (i : Fin 3) :
    (fourthBlockSwapToBase q ρ i).comp
        ((cwFourthCanonicalGrading K q).blockProj
          (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i))) =
      ((cwFourthCanonicalGrading K q).blockProj i
        (fixedModeRelabel swapFirstTwoPerm ρ i)).comp
        (cwFourthSwapToBase K q i) := by
  let b := cwFourthCanonicalBasis K q (swapFirstTwoPerm.symm i)
  refine b.ext ?_
  intro p
  change fourthBlockSwapToBase q ρ i
        ((cwFourthCanonicalGrading K q).blockProj
          (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i)) (b p)) =
      (cwFourthCanonicalGrading K q).blockProj i
        (fixedModeRelabel swapFirstTwoPerm ρ i)
        (cwFourthSwapToBase K q i (b p))
  by_cases hp : cwFourthPairGrade q p =
      ρ (swapFirstTwoPerm.symm i)
  · have hs : b p ∈ (cwFourthCanonicalGrading K q).classOf
        (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i)) :=
      Submodule.subset_span ⟨p, hp, rfl⟩
    have ht0 := cwFourthSwapToBase_mem_grade K q i
      (ρ (swapFirstTwoPerm.symm i)) (b p) hs
    have ht : cwFourthSwapToBase K q i (b p) ∈
        (cwFourthCanonicalGrading K q).classOf i
          (fixedModeRelabel swapFirstTwoPerm ρ i) := by
      simpa [fixedModeRelabel] using ht0
    rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ hs,
      TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ ht]
    apply Subtype.ext
    rfl
  · have hpt : cwFourthPairGrade q p ≠
        fixedModeRelabel swapFirstTwoPerm ρ i := by
      simpa [fixedModeRelabel] using hp
    have hs : b p ∈ (cwFourthCanonicalGrading K q).classOf
        (swapFirstTwoPerm.symm i) (cwFourthPairGrade q p) :=
      Submodule.subset_span ⟨p, rfl, rfl⟩
    have ht : cwFourthSwapToBase K q i (b p) ∈
        (cwFourthCanonicalGrading K q).classOf i
          (cwFourthPairGrade q p) :=
      cwFourthSwapToBase_mem_grade K q i
        (cwFourthPairGrade q p) (b p) hs
    rw [TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _ _
        (Ne.symm hp) _ hs,
      TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _ _
        (Ne.symm hpt) _ ht]
    exact map_zero _

private theorem fourthBlockSwapToBase_tensor
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9) :
    PiTensorProduct.map (fourthBlockSwapToBase q ρ)
        (TensorObj.permObj swapFirstTwoPerm
          ((cwFourthCanonicalGrading K q).blockSubtensor ρ)).t =
      ((cwFourthCanonicalGrading K q).blockSubtensor
        (fixedModeRelabel swapFirstTwoPerm ρ)).t := by
  change PiTensorProduct.map (fourthBlockSwapToBase q ρ)
      ((PiTensorProduct.reindex K
        (fun i ↦ (cwFourthCanonicalGrading K q).classOf i (ρ i))
        swapFirstTwoPerm)
        ((cwFourthCanonicalGrading K q).blockTensor ρ)) =
      (cwFourthCanonicalGrading K q).blockTensor
        (fixedModeRelabel swapFirstTwoPerm ρ)
  unfold TensorObj.TypeGrading.blockTensor
  rw [← PiTensorProduct.map_reindex
    (f := fun i ↦ (cwFourthCanonicalGrading K q).blockProj i (ρ i))
    swapFirstTwoPerm]
  have hcomp :
      (fun i ↦ (fourthBlockSwapToBase q ρ i).comp
        ((cwFourthCanonicalGrading K q).blockProj
          (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i)))) =
      (fun i ↦ ((cwFourthCanonicalGrading K q).blockProj i
        (fixedModeRelabel swapFirstTwoPerm ρ i)).comp
          (cwFourthSwapToBase K q i)) := by
    funext i
    exact fourthBlockSwapToBase_blockProj q ρ i
  rw [piMap_map_apply_fin3]
  rw [hcomp]
  rw [← piMap_map_apply_fin3]
  rw [cwFourthSwapToBase_tensor]

private theorem fourthBlockBaseToSwap_comp_swapToBase
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9)
    (i : Fin 3) :
    (fourthBlockBaseToSwap q ρ i).comp
        (fourthBlockSwapToBase q ρ i) =
      (LinearMap.id :
        (cwFourthCanonicalGrading K q).classOf
            (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i)) →ₗ[K]
          (cwFourthCanonicalGrading K q).classOf
            (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i))) := by
  ext x
  change cwFourthBaseToSwap K q i
      (cwFourthSwapToBase K q i x.1) = x.1
  exact LinearMap.congr_fun (cwFourthBaseToSwap_comp_swapToBase K q i) x.1

theorem cwFourth_swapped_block_iso
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9) :
    TensorObj.Isomorphic
      ((cwFourthCanonicalGrading K q).blockSubtensor
        (fixedModeRelabel swapFirstTwoPerm ρ))
      (TensorObj.permObj swapFirstTwoPerm
        ((cwFourthCanonicalGrading K q).blockSubtensor ρ)) := by
  constructor
  · exact ⟨fourthBlockSwapToBase q ρ,
      fourthBlockSwapToBase_tensor q ρ⟩
  · refine ⟨fourthBlockBaseToSwap q ρ, ?_⟩
    rw [← fourthBlockSwapToBase_tensor q ρ]
    have hcomp :
        (fun i ↦ (fourthBlockBaseToSwap q ρ i).comp
          (fourthBlockSwapToBase q ρ i)) =
        (fun i ↦ (LinearMap.id :
          (cwFourthCanonicalGrading K q).classOf
              (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i)) →ₗ[K]
            (cwFourthCanonicalGrading K q).classOf
              (swapFirstTwoPerm.symm i) (ρ (swapFirstTwoPerm.symm i)))) := by
      funext i
      exact fourthBlockBaseToSwap_comp_swapToBase q ρ i
    calc
      PiTensorProduct.map (fourthBlockBaseToSwap q ρ)
          (PiTensorProduct.map (fourthBlockSwapToBase q ρ)
            (TensorObj.permObj swapFirstTwoPerm
              ((cwFourthCanonicalGrading K q).blockSubtensor ρ)).t) =
        PiTensorProduct.map
          (fun i ↦ (fourthBlockBaseToSwap q ρ i).comp
            (fourthBlockSwapToBase q ρ i))
          (TensorObj.permObj swapFirstTwoPerm
            ((cwFourthCanonicalGrading K q).blockSubtensor ρ)).t :=
        piMap_map_apply_fin3
          (fourthBlockSwapToBase (K := K) q ρ)
          (fourthBlockBaseToSwap (K := K) q ρ) _
      _ = _ := by
        rw [hcomp, PiTensorProduct.map_id]
        rfl


private theorem fourthBlockBaseToSwap_tensor
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9) :
    PiTensorProduct.map (fourthBlockBaseToSwap q ρ)
      ((cwFourthCanonicalGrading K q).blockSubtensor
        (fixedModeRelabel swapFirstTwoPerm ρ)).t =
      (TensorObj.permObj swapFirstTwoPerm
        ((cwFourthCanonicalGrading K q).blockSubtensor ρ)).t := by
  rw [← fourthBlockSwapToBase_tensor q ρ, piMap_map_apply_fin3]
  simp only [fourthBlockBaseToSwap_comp_swapToBase, PiTensorProduct.map_id, LinearMap.id_apply]

private def flipCoordMap (K : Type u) [Field K] (A B : Type*) :
    (A × B → K) →ₗ[K] (B × A → K) where
  toFun f x := f (x.2, x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem flipCoord_single (K : Type u) [Field K]
    {A B : Type*} [DecidableEq A] [DecidableEq B] (a : A) (b : B) :
    flipCoordMap K A B (Pi.single (a,b) 1) = Pi.single (b,a) 1 := by
  ext x
  rcases x with ⟨x,y⟩
  simp [flipCoordMap, Pi.single_apply, Prod.mk.injEq, and_comm]

private noncomputable def mmSwapMap (K : Type u) [Field K] (D : ℕ) :
    ∀ s, (TensorObj.permObj swapFirstTwoPerm (MMObj K 1 1 D)).V s →ₗ[K]
      (MMObj K D 1 1).V s
  | 0 => flipCoordMap K (Fin 1) (Fin D)
  | 1 => flipCoordMap K (Fin 1) (Fin 1)
  | 2 => flipCoordMap K (Fin D) (Fin 1)

private theorem mmSwapMap_tensor (K : Type u) [Field K] (D : ℕ) :
    PiTensorProduct.map (mmSwapMap K D)
      (TensorObj.permObj swapFirstTwoPerm (MMObj K 1 1 D)).t =
      (MMObj K D 1 1).t := by
  classical
  change PiTensorProduct.map (mmSwapMap K D)
    ((PiTensorProduct.reindex K _ swapFirstTwoPerm) (MMTensor K 1 1 D)) = MMTensor K D 1 1
  unfold MMTensor
  simp only [Fin.sum_univ_one, map_sum]
  erw [map_sum (PiTensorProduct.map (mmSwapMap K D))]
  apply Finset.sum_congr rfl
  intro c _
  rw [PiTensorProduct.reindex_tprod]
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s <;> exact flipCoord_single K _ _



open MME.CompleteSplit.CWFourth

private theorem fourthBlockBaseToSwap_Z
    {K : Type u} [Field K] (q : ℕ) (j k : Fin 9)
    (v : (cwFourthConstituent K q j 0 k).V 2) :
    fourthBlockBaseToSwap q (cwFourthBlockType 0 j k) 2 v =
      (show (cwFourthConstituent K q 0 j k).V 2 from v) := by
  apply Subtype.ext
  change TensorProduct.map (TensorProduct.map LinearMap.id LinearMap.id)
    (TensorProduct.map LinearMap.id LinearMap.id) v.val = v.val
  simp

private def YRouterAt (K : Type u) [Field K] (q : ℕ) (σ : Fin 3 → Fin 9) : Prop :=
    ∃ coord : LiftedCoarseCoordinate.{u} q (σ 2) ↪
        Fin (Fintype.card (LiftedCoarseCoordinate.{u} q (σ 2))),
      ∃ maps : ∀ s, ((cwFourthCanonicalGrading K q).blockSubtensor σ).V s →ₗ[K]
        (MMObj K (Fintype.card (LiftedCoarseCoordinate.{u} q (σ 2))) 1 1).V s,
        PiTensorProduct.map maps ((cwFourthCanonicalGrading K q).blockSubtensor σ).t =
          (MMObj K (Fintype.card (LiftedCoarseCoordinate.{u} q (σ 2))) 1 1).t ∧
        ∀ p, maps 2 (((coarseClassBasis K q 2 (σ 2)).reindex Equiv.ulift.symm) p) =
          (Pi.single ((0 : Fin 1), coord p) 1 :
            Fin 1 × Fin (Fintype.card (LiftedCoarseCoordinate.{u} q (σ 2))) → K)

private theorem yzero_router
    (K : Type u) [Field K] (q : ℕ) (j k : Fin 9) (hjk : j.val + k.val = 8) :
    ∃ coord : LiftedCoarseCoordinate.{u} q k ↪
        Fin (Fintype.card (LiftedCoarseCoordinate.{u} q k)),
      ∃ maps : ∀ s, (cwFourthConstituent K q j 0 k).V s →ₗ[K]
        (MMObj K (Fintype.card (LiftedCoarseCoordinate.{u} q k)) 1 1).V s,
        PiTensorProduct.map maps (cwFourthConstituent K q j 0 k).t =
          (MMObj K (Fintype.card (LiftedCoarseCoordinate.{u} q k)) 1 1).t ∧
        ∀ p, maps 2 (constituentBasis K q j 0 k 2 p) =
          (Pi.single ((0 : Fin 1), coord p) 1 :
            Fin 1 × Fin (Fintype.card (LiftedCoarseCoordinate.{u} q k)) → K) := by
  classical
  obtain ⟨coord,router,ht,hz⟩ := mme_CW_fourth_Xzero_exact_Z_basis_router K q j k hjk
  let D := Fintype.card (LiftedCoarseCoordinate.{u} q k)
  let ρ := cwFourthBlockType 0 j k
  let S := (cwFourthCanonicalGrading K q).blockSubtensor (fixedModeRelabel swapFirstTwoPerm ρ)
  have hρ : fixedModeRelabel swapFirstTwoPerm ρ = cwFourthBlockType j 0 k := by
    funext s
    fin_cases s <;> rfl
  change YRouterAt K q (cwFourthBlockType j 0 k)
  rw [← hρ]
  unfold YRouterAt
  let fs := fourthBlockBaseToSwap (K := K) q ρ
  let permRouter := fun s ↦ router (swapFirstTwoPerm.symm s)
  let maps := fun s ↦ (mmSwapMap K D s).comp ((permRouter s).comp (fs s))
  refine ⟨coord, maps, ?_, ?_⟩
  · change PiTensorProduct.map (fun s ↦ (mmSwapMap K D s).comp ((permRouter s).comp (fs s))) S.t = _
    rw [← piMap_map_apply_fin3, ← piMap_map_apply_fin3]
    have hf := fourthBlockBaseToSwap_tensor (K := K) q ρ
    change PiTensorProduct.map fs S.t = _ at hf
    erw [hf]
    change PiTensorProduct.map (mmSwapMap K D)
      (PiTensorProduct.map permRouter
        ((PiTensorProduct.reindex K _ swapFirstTwoPerm) (cwFourthConstituent K q 0 j k).t)) = _
    erw [PiTensorProduct.map_reindex (f := router) swapFirstTwoPerm]
    erw [ht]
    exact mmSwapMap_tensor K D
  · intro p
    change flipCoordMap K (Fin D) (Fin 1)
      (router 2 (fourthBlockBaseToSwap q (cwFourthBlockType 0 j k) 2
        (constituentBasis K q j 0 k 2 p))) = _
    rw [fourthBlockBaseToSwap_Z]
    change flipCoordMap K (Fin D) (Fin 1)
      (router 2 (constituentBasis K q 0 j k 2 p)) = _
    rw [hz]
    exact flipCoord_single K _ _

end MME.StothersFourth.NumericM5
open MME.StothersFourth MME.CompleteSplit.CWFourth

theorem solution
    (K : Type u) [Field K] (q : ℕ) (j k : Fin 9) (hjk : j.val + k.val = 8) :
    ∃ coord : LiftedCoarseCoordinate.{u} q k ↪
        Fin (Fintype.card (LiftedCoarseCoordinate.{u} q k)),
      ∃ maps : ∀ s, (cwFourthConstituent K q j 0 k).V s →ₗ[K]
        (MMObj K (Fintype.card (LiftedCoarseCoordinate.{u} q k)) 1 1).V s,
        PiTensorProduct.map maps (cwFourthConstituent K q j 0 k).t =
          (MMObj K (Fintype.card (LiftedCoarseCoordinate.{u} q k)) 1 1).t ∧
        ∀ p, maps 2 (constituentBasis K q j 0 k 2 p) =
          (Pi.single ((0 : Fin 1), coord p) 1 :
            Fin 1 × Fin (Fintype.card (LiftedCoarseCoordinate.{u} q k)) → K) := by
  exact MME.StothersFourth.NumericM5.yzero_router K q j k hjk
