-- Prove2me | solution 1 for mme_complete_split_CW_square_cyclic_basis_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T04:07:15.969632+00:00
-- url     : https://prove2.me/submissions/1926fd9a-77cf-412a-88fd-a36144377e2e

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_permutation
import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct TensorProduct Module BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace MME.CanonicalCyclicBasis

private noncomputable def cwCyclicToBaseLocal
    (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3,
      CWSpace K q (cyclicPerm.symm i) →ₗ[K] CWSpace K q i :=
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

private theorem cwCyclicToBaseLocal_monom
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    PiTensorProduct.map (cwCyclicToBaseLocal K q)
      ((PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
        (CWMonom K q a b c)) = CWMonom K q c a b := by
  unfold CWMonom
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem cwCyclicToBaseLocal_tensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwCyclicToBaseLocal K q)
      ((PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
        (CWTensor K q)) = CWTensor K q := by
  unfold CWTensor
  simp only [map_add, map_sum, cwCyclicToBaseLocal_monom]
  let O : Fin (q + 2) := ⟨0, by omega⟩
  have hsum :
      (∑ i : Fin q,
        let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
        CWMonom K q M O M + CWMonom K q M M O +
          CWMonom K q O M M) =
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

private noncomputable def cwSquareCyclicToBaseLocal
    (K : Type u) [Field K] (q : ℕ) : ∀ i : Fin 3,
    ((TensorObj.kron (CWObj K q) (CWObj K q)).V
      (cyclicPerm.symm i)) →ₗ[K]
    ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) :=
  fun i ↦ TensorProduct.map
    (cwCyclicToBaseLocal K q i) (cwCyclicToBaseLocal K q i)

private theorem cwSquareCyclicToBaseLocal_tensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (cwSquareCyclicToBaseLocal K q)
      ((PiTensorProduct.reindex K
        (TensorObj.kron (CWObj K q) (CWObj K q)).V
        cyclicPerm)
        (TensorObj.kron (CWObj K q) (CWObj K q)).t) =
      (TensorObj.kron (CWObj K q) (CWObj K q)).t := by
  change PiTensorProduct.map (cwSquareCyclicToBaseLocal K q)
      ((PiTensorProduct.reindex K
        (fun i ↦ CWSpace K q i ⊗[K] CWSpace K q i)
        cyclicPerm)
        (interchange (CWTensor K q) (CWTensor K q))) =
      interchange (CWTensor K q) (CWTensor K q)
  rw [reindex_interchange]
  change PiTensorProduct.map
      (fun i ↦ TensorProduct.map
        (cwCyclicToBaseLocal K q i) (cwCyclicToBaseLocal K q i))
      (interchange
        ((PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
          (CWTensor K q))
        ((PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
          (CWTensor K q))) = _
  rw [TensorObj.TypeGrading.kronMap_interchange,
    cwCyclicToBaseLocal_tensor]

open MME.CompleteSplitCanonicalSquare

private noncomputable def cyclicClassEquiv
    (K : Type u) [Field K] (q : ℕ) (rho : Fin 3 → Fin 5) (i : Fin 3) :
    (TensorObj.permObj cyclicPerm (obj K q rho)).V i ≃ₗ[K]
      (obj K q (fun j ↦ rho (cyclicPerm.symm j))).V i :=
  match i with
  | ⟨0, _⟩ => LinearEquiv.refl K _
  | ⟨1, _⟩ => LinearEquiv.refl K _
  | ⟨2, _⟩ => LinearEquiv.refl K _

private theorem cyclicClassEquiv_basis
    (K : Type u) [Field K] (q : ℕ) (rho : Fin 3 → Fin 5) (i : Fin 3)
    (p : Coord.{u} q rho (cyclicPerm.symm i)) :
    cyclicClassEquiv K q rho i (basis K q rho (cyclicPerm.symm i) p) =
      basis K q (fun j ↦ rho (cyclicPerm.symm j)) i p := by
  fin_cases i <;> rfl

private theorem cyclicClassEquiv_blockProj
    (K : Type u) [Field K] (q : ℕ) (rho : Fin 3 → Fin 5) (i : Fin 3) :
    (cyclicClassEquiv K q rho i).toLinearMap.comp
        ((cwSquareCanonicalGrading K q).blockProj
          (cyclicPerm.symm i) (rho (cyclicPerm.symm i))) =
      ((cwSquareCanonicalGrading K q).blockProj i
        (rho (cyclicPerm.symm i))).comp (cwSquareCyclicToBaseLocal K q i) := by
  fin_cases i <;>
    change LinearMap.comp LinearMap.id _ =
      LinearMap.comp _ (TensorProduct.map LinearMap.id LinearMap.id)
  all_goals rw [TensorProduct.map_id]
  all_goals rfl

private theorem cyclicClassEquiv_tensor
    (K : Type u) [Field K] (q : ℕ) (rho : Fin 3 → Fin 5) :
    PiTensorProduct.map (fun i ↦ (cyclicClassEquiv K q rho i).toLinearMap)
        (TensorObj.permObj cyclicPerm (obj K q rho)).t =
      (obj K q (fun i ↦ rho (cyclicPerm.symm i))).t := by
  change PiTensorProduct.map (fun i ↦ (cyclicClassEquiv K q rho i).toLinearMap)
      ((PiTensorProduct.reindex K
        (fun i ↦ (cwSquareCanonicalGrading K q).classOf i (rho i)) cyclicPerm)
        ((cwSquareCanonicalGrading K q).blockTensor rho)) =
    (cwSquareCanonicalGrading K q).blockTensor (fun i ↦ rho (cyclicPerm.symm i))
  unfold TensorObj.TypeGrading.blockTensor
  rw [← PiTensorProduct.map_reindex
    (f := fun i ↦ (cwSquareCanonicalGrading K q).blockProj i (rho i)) cyclicPerm]
  have hcomp :
      (fun i ↦ (cyclicClassEquiv K q rho i).toLinearMap.comp
        ((cwSquareCanonicalGrading K q).blockProj
          (cyclicPerm.symm i) (rho (cyclicPerm.symm i)))) =
      (fun i ↦ ((cwSquareCanonicalGrading K q).blockProj i
        (rho (cyclicPerm.symm i))).comp (cwSquareCyclicToBaseLocal K q i)) := by
    funext i
    exact cyclicClassEquiv_blockProj K q rho i
  have hfirst := LinearMap.congr_fun (PiTensorProduct.map_comp
    (f := fun i ↦ (cwSquareCanonicalGrading K q).blockProj
      (cyclicPerm.symm i) (rho (cyclicPerm.symm i)))
    (g := fun i ↦ (cyclicClassEquiv K q rho i).toLinearMap))
    ((PiTensorProduct.reindex K (TensorObj.kron (CWObj K q) (CWObj K q)).V
      cyclicPerm) (TensorObj.kron (CWObj K q) (CWObj K q)).t)
  simp only [LinearMap.comp_apply] at hfirst
  erw [← hfirst, hcomp]
  have hsecond := LinearMap.congr_fun (PiTensorProduct.map_comp
    (f := cwSquareCyclicToBaseLocal K q)
    (g := fun i ↦ (cwSquareCanonicalGrading K q).blockProj i
      (rho (cyclicPerm.symm i))))
    ((PiTensorProduct.reindex K (TensorObj.kron (CWObj K q) (CWObj K q)).V
      cyclicPerm) (TensorObj.kron (CWObj K q) (CWObj K q)).t)
  simp only [LinearMap.comp_apply] at hsecond
  exact hsecond.trans (congrArg
    (PiTensorProduct.map (fun i ↦ (cwSquareCanonicalGrading K q).blockProj i
      (rho (cyclicPerm.symm i)))) (cwSquareCyclicToBaseLocal_tensor K q))

end MME.CanonicalCyclicBasis

open MME.CompleteSplitCanonicalSquare MME.CanonicalCyclicBasis in
theorem solution
    (K : Type u) [Field K] (q : ℕ) (rho : Fin 3 → Fin 5) :
    ∃ maps : ∀ i : Fin 3,
        (TensorObj.permObj cyclicPerm (obj K q rho)).V i ≃ₗ[K]
          (obj K q (fun j ↦ rho (cyclicPerm.symm j))).V i,
      PiTensorProduct.map (fun i ↦ (maps i).toLinearMap)
          (TensorObj.permObj cyclicPerm (obj K q rho)).t =
        (obj K q (fun j ↦ rho (cyclicPerm.symm j))).t ∧
      (∀ (i : Fin 3) (p : Coord.{u} q rho (cyclicPerm.symm i)),
        maps i (basis K q rho (cyclicPerm.symm i) p) =
          basis K q (fun j ↦ rho (cyclicPerm.symm j)) i p) ∧
      (∀ (i : Fin 3) (p : Coord.{u} q rho (cyclicPerm.symm i)),
        label q (fun j ↦ rho (cyclicPerm.symm j)) i p =
          label q rho (cyclicPerm.symm i) p) := by
  exact ⟨cyclicClassEquiv K q rho, cyclicClassEquiv_tensor K q rho,
    cyclicClassEquiv_basis K q rho, fun _ _ ↦ rfl⟩
