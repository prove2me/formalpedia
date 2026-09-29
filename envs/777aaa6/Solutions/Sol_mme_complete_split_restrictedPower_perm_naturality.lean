-- Prove2me | solution 1 for mme_complete_split_restrictedPower_perm_naturality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T03:40:09.869656+00:00
-- url     : https://prove2.me/submissions/a97d4865-189d-43e1-ae47-398dc64d3e27

import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_perm_kronPow_mode_equiv_preserves_tensor
import Theorems.Thm_mme_perm_kronPow_mode_equiv_recursive_basis
import Definitions.Def_mme_TypeGrading_permutation

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped Classical NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem disallowed_projection_zero
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (I i) K (T.V i))
    (allowed : (i : Fin 3) → I i → Prop) (i : Fin 3) (j : I i)
    (hj : ¬ allowed i j) :
    (T.basisAllAllowedGrading b allowed).blockProj i 0 (b i j) = 0 := by
  classical
  let G := T.basisAllAllowedGrading b allowed
  have hx : b i j ∈ G.classOf i 1 := by
    change b i j ∈ cwBasisGrade (b i)
      (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 1
    exact Submodule.subset_span
      ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
  exact (G.is_internal i).ofBijective_coeLinearMap_of_mem_ne
    (show (1 : Fin 2) ≠ 0 by decide) hx

private theorem allowed_restrict_of_basis_map
    {K : Type u} [Field K] (T S : TensorObj K 3) {I : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (I i) K (T.V i))
    (c : (i : Fin 3) → Basis (I i) K (S.V i))
    (f : (i : Fin 3) → T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t)
    (hbasis : ∀ i j, f i (b i j) = c i j)
    (allowed : (i : Fin 3) → I i → Prop) :
    TensorObj.Restrict (S.basisAllAllowedSubtensor c allowed)
      (T.basisAllAllowedSubtensor b allowed) := by
  classical
  let G := S.basisAllAllowedGrading c allowed
  let maps := fun i ↦ (G.blockProj i 0).comp (f i)
  have hmap : PiTensorProduct.map maps T.t =
      (S.basisAllAllowedSubtensor c allowed).t := by
    change PiTensorProduct.map (fun i ↦ (G.blockProj i 0).comp (f i)) T.t = _
    rw [PiTensorProduct.map_comp]
    change PiTensorProduct.map (fun i ↦ G.blockProj i 0)
      (PiTensorProduct.map f T.t) = _
    rw [hf]
    rfl
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes
    T (S.basisAllAllowedSubtensor c allowed) b allowed maps hmap
  intro i j hj
  change G.blockProj i 0 (f i (b i j)) = 0
  rw [hbasis]
  exact disallowed_projection_zero S c allowed i j hj

private theorem allowed_iso_of_basis_equiv
    {K : Type u} [Field K] (T S : TensorObj K 3) {I : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (I i) K (T.V i))
    (c : (i : Fin 3) → Basis (I i) K (S.V i))
    (E : (i : Fin 3) → T.V i ≃ₗ[K] S.V i)
    (hE : PiTensorProduct.map (fun i ↦ (E i).toLinearMap) T.t = S.t)
    (hbasis : ∀ i j, E i (b i j) = c i j)
    (allowed : (i : Fin 3) → I i → Prop) :
    TensorObj.Isomorphic (T.basisAllAllowedSubtensor b allowed)
      (S.basisAllAllowedSubtensor c allowed) := by
  have hcomp :
      (fun i ↦ (E i).symm.toLinearMap.comp (E i).toLinearMap) =
        (fun i ↦ (LinearMap.id : T.V i →ₗ[K] T.V i)) := by
    funext i
    ext x
    exact (E i).symm_apply_apply x
  have hEinv : PiTensorProduct.map (fun i ↦ (E i).symm.toLinearMap) S.t = T.t := by
    calc
      _ = PiTensorProduct.map (fun i ↦ (E i).symm.toLinearMap)
          (PiTensorProduct.map (fun i ↦ (E i).toLinearMap) T.t) := by rw [hE]
      _ = PiTensorProduct.map
          (fun i ↦ (E i).symm.toLinearMap.comp (E i).toLinearMap) T.t := by
        exact (LinearMap.congr_fun
          (PiTensorProduct.map_comp
            (f := fun i ↦ (E i).toLinearMap)
            (g := fun i ↦ (E i).symm.toLinearMap)) T.t).symm
      _ = T.t := by
        rw [hcomp]
        exact LinearMap.congr_fun (PiTensorProduct.map_id (R := K) (s := T.V)) T.t
  have hbinv : ∀ i j, (E i).symm (c i j) = b i j := by
    intro i j
    apply (E i).injective
    rw [LinearEquiv.apply_symm_apply, hbasis]
  exact ⟨allowed_restrict_of_basis_map S T c b
      (fun i ↦ (E i).symm.toLinearMap) hEinv hbinv allowed,
    allowed_restrict_of_basis_map T S b c
      (fun i ↦ (E i).toLinearMap) hE hbasis allowed⟩

/-- Mode permutation preserves the entire complete-word restriction.
The basis-word index and its ordered fine letters are unchanged. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    (e : Equiv.Perm (Fin 3)) {I : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (I i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → I i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Isomorphic
      (restrictedPower (TensorObj.permObj e T)
        (fun i ↦ b (e.symm i)) (fun i ↦ label (e.symm i))
        (fun i ↦ beta (e.symm i)) epsilon N)
      (TensorObj.permObj e (restrictedPower T b label beta epsilon N)) := by
  classical
  have hfilter := allowed_iso_of_basis_equiv
    ((TensorObj.permObj e T).kronPow N) (TensorObj.permObj e (T.kronPow N))
    (fun i ↦ kronPowModeBasis (TensorObj.permObj e T) i (b (e.symm i)) N)
    (fun i ↦ kronPowModeBasis T (e.symm i) (b (e.symm i)) N)
    (fun i ↦ permKronPowModeEquiv e T i N)
    (mme_perm_kronPow_mode_equiv_preserves_tensor e T N)
    (fun i w ↦ mme_perm_kronPow_mode_equiv_recursive_basis e T i (b (e.symm i)) N w)
    (fun i ↦ ApproxConsistent (label (e.symm i)) (beta (e.symm i)) epsilon)
  have hperm := TensorObj.TypeGrading.permObjGrading_blockSubtensor_iso
    ((T.kronPow N).basisAllAllowedGrading
      (fun i ↦ kronPowModeBasis T i (b i) N)
      (fun i ↦ ApproxConsistent (label i) (beta i) epsilon)) e (fun _ ↦ 0)
  exact hfilter.trans hperm
