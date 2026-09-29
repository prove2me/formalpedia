-- Prove2me | solution 1 for mme_complete_split_CW_square_cyclic_profile_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T04:27:30.810709+00:00
-- url     : https://prove2.me/submissions/a9475b82-f4a0-4145-acb3-f4dfb42b0712

import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_permutation
import Theorems.Thm_mme_complete_split_restrictedPower_perm_naturality
import Theorems.Thm_mme_complete_split_CW_square_cyclic_basis_transport
import Theorems.Thm_mme_complete_split_restrictedPower_basis_router

open MME MME.CompleteSplit Module
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem inverse_maps_preserve_tensor
    {K : Type u} [Field K] (T S : TensorObj K 3)
    (E : (i : Fin 3) → T.V i ≃ₗ[K] S.V i)
    (hE : PiTensorProduct.map (fun i ↦ (E i).toLinearMap) T.t = S.t) :
    PiTensorProduct.map (fun i ↦ (E i).symm.toLinearMap) S.t = T.t := by
  have hcomp :
      (fun i ↦ (E i).symm.toLinearMap.comp (E i).toLinearMap) =
        (fun i ↦ (LinearMap.id : T.V i →ₗ[K] T.V i)) := by
    funext i
    ext x
    exact (E i).symm_apply_apply x
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

private theorem restricted_power_iso_of_basis_equiv
    {K : Type u} [Field K] (T S : TensorObj K 3) {I : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (I i) K (T.V i))
    (c : (i : Fin 3) → Basis (I i) K (S.V i))
    (E : (i : Fin 3) → T.V i ≃ₗ[K] S.V i)
    (hE : PiTensorProduct.map (fun i ↦ (E i).toLinearMap) T.t = S.t)
    (hbasis : ∀ i j, E i (b i j) = c i j) {ell : ℕ}
    (labelT : (i : Fin 3) → I i → CompleteWord ell)
    (labelS : (i : Fin 3) → I i → CompleteWord ell)
    (hlabel : ∀ i j, labelS i j = labelT i j)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Isomorphic (restrictedPower S c labelS beta epsilon N)
      (restrictedPower T b labelT beta epsilon N) := by
  have hbinv : ∀ i j, (E i).symm (c i j) = b i j := by
    intro i j
    apply (E i).injective
    rw [LinearEquiv.apply_symm_apply, hbasis]
  exact ⟨mme_complete_split_restrictedPower_basis_router T S b c
      (fun i ↦ (E i).toLinearMap) hE (fun _ j ↦ j) hbasis
      labelT labelS hlabel beta epsilon N,
    mme_complete_split_restrictedPower_basis_router S T c b
      (fun i ↦ (E i).symm.toLinearMap) (inverse_maps_preserve_tensor T S E hE)
      (fun _ j ↦ j) hbinv labelS labelT (fun i j ↦ (hlabel i j).symm)
      beta epsilon N⟩

private theorem cyclic_transport_once
    (K : Type u) [Field K] (q : ℕ) (rho : Fin 3 → Fin 5)
    (beta : Fin 3 → Profile 2) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Isomorphic
      (CompleteSplitCanonicalSquare.restrictedPower K q
        (fun i ↦ rho (cyclicPerm.symm i))
        (fun i ↦ beta (cyclicPerm.symm i)) epsilon N)
      (TensorObj.permObj cyclicPerm
        (CompleteSplitCanonicalSquare.restrictedPower K q rho beta epsilon N)) := by
  obtain ⟨maps, hmaps, hbasis, hlabel⟩ :=
    mme_complete_split_CW_square_cyclic_basis_transport K q rho
  have hprofile := restricted_power_iso_of_basis_equiv
    (TensorObj.permObj cyclicPerm (CompleteSplitCanonicalSquare.obj K q rho))
    (CompleteSplitCanonicalSquare.obj K q (fun i ↦ rho (cyclicPerm.symm i)))
    (fun i ↦ CompleteSplitCanonicalSquare.basis K q rho (cyclicPerm.symm i))
    (CompleteSplitCanonicalSquare.basis K q (fun i ↦ rho (cyclicPerm.symm i)))
    maps hmaps hbasis
    (fun i ↦ CompleteSplitCanonicalSquare.label q rho (cyclicPerm.symm i))
    (CompleteSplitCanonicalSquare.label q (fun i ↦ rho (cyclicPerm.symm i)))
    hlabel (fun i ↦ beta (cyclicPerm.symm i)) epsilon N
  have hnatural := mme_complete_split_restrictedPower_perm_naturality
    (CompleteSplitCanonicalSquare.obj K q rho) cyclicPerm
    (CompleteSplitCanonicalSquare.basis K q rho)
    (CompleteSplitCanonicalSquare.label q rho) beta epsilon N
  exact hprofile.trans hnatural

private theorem permObj_trans_iso_pair
    {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj e' (TensorObj.permObj e X))
      (TensorObj.permObj (e.trans e') X) := by
  have ht : (TensorObj.permObj e' (TensorObj.permObj e X)).t =
      (TensorObj.permObj (e.trans e') X).t :=
    PiTensorProduct.reindex_reindex e e' X.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj (e.trans e') X).V))
      (TensorObj.permObj (e.trans e') X).t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj e' (TensorObj.permObj e X)).V))
      (TensorObj.permObj e' (TensorObj.permObj e X)).t
    exact hmap.trans ht

/-- Both nontrivial cyclic orientations preserve the literal canonical
CW-square complete-profile source for every q and every finite power. -/
theorem solution
    (K : Type u) [Field K] (q : ℕ) (rho : Fin 3 → Fin 5)
    (e : Equiv.Perm (Fin 3))
    (he : e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm)
    (beta : Fin 3 → Profile 2) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Isomorphic
      (CompleteSplitCanonicalSquare.restrictedPower K q
        (fun i ↦ rho (e.symm i)) (fun i ↦ beta (e.symm i)) epsilon N)
      (TensorObj.permObj e
        (CompleteSplitCanonicalSquare.restrictedPower K q rho beta epsilon N)) := by
  rcases he with rfl | rfl
  · exact cyclic_transport_once K q rho beta epsilon N
  · exact (cyclic_transport_once K q
      (fun i ↦ rho (cyclicPerm.symm i)) (fun i ↦ beta (cyclicPerm.symm i))
      epsilon N).trans
      ((TensorObj.permObj_isomorphic cyclicPerm
        (cyclic_transport_once K q rho beta epsilon N)).trans
        (permObj_trans_iso_pair cyclicPerm cyclicPerm
          (CompleteSplitCanonicalSquare.restrictedPower K q rho beta epsilon N)))
