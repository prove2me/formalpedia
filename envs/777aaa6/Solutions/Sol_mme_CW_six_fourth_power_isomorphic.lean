-- Prove2me | solution 1 for mme_CW_six_fourth_power_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:36:53.801868+00:00
-- url     : https://prove2.me/submissions/857b5126-e4c9-4cc0-b97d-5d214d908a7e

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME PiTensorProduct BigOperators
universe u
set_option autoImplicit false

namespace CWRawSymmetry

/-- The canonical identity equivalence from a cyclically reindexed CW mode
space back to the mode carrying the same coordinate space. -/
noncomputable def cwCyclicModeEquiv
    (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3,
      CWSpace K q (cyclicPerm.symm i) ≃ₗ[K] CWSpace K q i
  | ⟨0, _⟩ => LinearEquiv.refl K _
  | ⟨1, _⟩ => LinearEquiv.refl K _
  | ⟨2, _⟩ => LinearEquiv.refl K _

/-- Reindexing a CW monomial and applying the canonical mode
identifications rotates its three coordinate labels. -/
theorem map_reindex_CWMonom_cyclic
    (K : Type u) [Field K] (q : ℕ)
    (a b c : Fin (q + 2)) :
    PiTensorProduct.map
        (fun i ↦ (cwCyclicModeEquiv K q i).toLinearMap)
        ((PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
          (CWMonom K q a b c)) =
      CWMonom K q c a b := by
  rw [CWMonom, PiTensorProduct.reindex_tprod,
    PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

/-- The full CW tensor is fixed by one cyclic mode rotation after the
canonical mode-space identifications. -/
theorem map_reindex_CWTensor_cyclic
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map
        (fun i ↦ (cwCyclicModeEquiv K q i).toLinearMap)
        ((PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
          (CWTensor K q)) =
      CWTensor K q := by
  let O : Fin (q + 2) := ⟨0, by omega⟩
  let T : Fin (q + 2) := ⟨q + 1, by omega⟩
  change
    PiTensorProduct.map
        (fun i ↦ (cwCyclicModeEquiv K q i).toLinearMap)
        ((PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
          ((∑ i : Fin q,
              let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
              CWMonom K q O M M + CWMonom K q M O M +
                CWMonom K q M M O) +
            CWMonom K q O O T + CWMonom K q O T O +
              CWMonom K q T O O)) =
      (∑ i : Fin q,
          let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
          CWMonom K q O M M + CWMonom K q M O M +
            CWMonom K q M M O) +
        CWMonom K q O O T + CWMonom K q O T O +
          CWMonom K q T O O
  simp only [map_add, map_sum, map_reindex_CWMonom_cyclic]
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
    dsimp only
    abel
  rw [hsum]
  abel

/-- Cyclically permuting the modes of a CW tensor gives an isomorphic copy
of the same tensor object. -/
theorem CWObj_permObj_cyclic
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm (CWObj K q))
      (CWObj K q) := by
  let f : ∀ i,
      (TensorObj.permObj cyclicPerm (CWObj K q)).V i →ₗ[K]
        (CWObj K q).V i :=
    fun i ↦ (cwCyclicModeEquiv K q i).toLinearMap
  let g : ∀ i,
      (CWObj K q).V i →ₗ[K]
        (TensorObj.permObj cyclicPerm (CWObj K q)).V i :=
    fun i ↦ (cwCyclicModeEquiv K q i).symm.toLinearMap
  have hcomp : (fun i ↦ (g i).comp (f i)) =
      (fun i ↦ LinearMap.id) := by
    funext i
    apply LinearMap.ext
    intro x
    exact (cwCyclicModeEquiv K q i).symm_apply_apply x
  have hf :
      PiTensorProduct.map f
          (TensorObj.permObj cyclicPerm (CWObj K q)).t =
        (CWObj K q).t := by
    exact map_reindex_CWTensor_cyclic K q
  refine ⟨⟨g, ?_⟩, ⟨f, hf⟩⟩
  rw [← hf, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, hcomp,
    PiTensorProduct.map_id, LinearMap.id_coe, id_eq]


/-- The canonical identity equivalence from a first-two-swapped CW mode
space back to the corresponding coordinate space. -/
noncomputable def cwSwapFirstTwoModeEquiv
    (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3,
      CWSpace K q (swapFirstTwoPerm.symm i) ≃ₗ[K] CWSpace K q i
  | ⟨0, _⟩ => LinearEquiv.refl K _
  | ⟨1, _⟩ => LinearEquiv.refl K _
  | ⟨2, _⟩ => LinearEquiv.refl K _

/-- Reindexing a CW monomial by the first-two transposition exchanges its
first two coordinate labels. -/
theorem map_reindex_CWMonom_swapFirstTwo
    (K : Type u) [Field K] (q : ℕ)
    (a b c : Fin (q + 2)) :
    PiTensorProduct.map
        (fun i ↦ (cwSwapFirstTwoModeEquiv K q i).toLinearMap)
        ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
          (CWMonom K q a b c)) =
      CWMonom K q b a c := by
  rw [CWMonom, PiTensorProduct.reindex_tprod,
    PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

/-- The full CW tensor is fixed by exchanging its first two modes. -/
theorem map_reindex_CWTensor_swapFirstTwo
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map
        (fun i ↦ (cwSwapFirstTwoModeEquiv K q i).toLinearMap)
        ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
          (CWTensor K q)) =
      CWTensor K q := by
  let O : Fin (q + 2) := ⟨0, by omega⟩
  let T : Fin (q + 2) := ⟨q + 1, by omega⟩
  change
    PiTensorProduct.map
        (fun i ↦ (cwSwapFirstTwoModeEquiv K q i).toLinearMap)
        ((PiTensorProduct.reindex K (CWSpace K q) swapFirstTwoPerm)
          ((∑ i : Fin q,
              let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
              CWMonom K q O M M + CWMonom K q M O M +
                CWMonom K q M M O) +
            CWMonom K q O O T + CWMonom K q O T O +
              CWMonom K q T O O)) =
      (∑ i : Fin q,
          let M : Fin (q + 2) := ⟨i.val + 1, by omega⟩
          CWMonom K q O M M + CWMonom K q M O M +
            CWMonom K q M M O) +
        CWMonom K q O O T + CWMonom K q O T O +
          CWMonom K q T O O
  simp only [map_add, map_sum, map_reindex_CWMonom_swapFirstTwo]
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
    dsimp only
    abel
  rw [hsum]
  abel

/-- Swapping the first two modes of a CW tensor gives an isomorphic copy
of the same tensor object. -/
theorem CWObj_permObj_swapFirstTwo
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj swapFirstTwoPerm (CWObj K q))
      (CWObj K q) := by
  let f : ∀ i,
      (TensorObj.permObj swapFirstTwoPerm (CWObj K q)).V i →ₗ[K]
        (CWObj K q).V i :=
    fun i ↦ (cwSwapFirstTwoModeEquiv K q i).toLinearMap
  let g : ∀ i,
      (CWObj K q).V i →ₗ[K]
        (TensorObj.permObj swapFirstTwoPerm (CWObj K q)).V i :=
    fun i ↦ (cwSwapFirstTwoModeEquiv K q i).symm.toLinearMap
  have hcomp : (fun i ↦ (g i).comp (f i)) =
      (fun i ↦ LinearMap.id) := by
    funext i
    apply LinearMap.ext
    intro x
    exact (cwSwapFirstTwoModeEquiv K q i).symm_apply_apply x
  have hf :
      PiTensorProduct.map f
          (TensorObj.permObj swapFirstTwoPerm (CWObj K q)).t =
        (CWObj K q).t := by
    exact map_reindex_CWTensor_swapFirstTwo K q
  refine ⟨⟨g, ?_⟩, ⟨f, hf⟩⟩
  rw [← hf, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, hcomp,
    PiTensorProduct.map_id, LinearMap.id_coe, id_eq]

private theorem permObj_trans_iso_local
    {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj e' (TensorObj.permObj e X))
      (TensorObj.permObj (e.trans e') X) := by
  have ht : (TensorObj.permObj e' (TensorObj.permObj e X)).t =
      (TensorObj.permObj (e.trans e') X).t := by
    exact PiTensorProduct.reindex_reindex e e' X.t
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


end CWRawSymmetry

/-- Six symmetrized fourth powers have exactly twenty-four elementary CW factors. -/
theorem solution
    {K : Type u} [Field K] (q n : ℕ) :
    TensorObj.Isomorphic
      ((sixSymmetrization (StothersFourth.cwFourthObj K q)).kronPow n)
      ((CWObj K q).kronPow (24 * n)) := by
  let x := TensorQ.toQ (CWObj K q)
  have hc : TensorQ.permAut cyclicPerm x = x :=
    TensorQ.toQ_eq_iff.2 (CWRawSymmetry.CWObj_permObj_cyclic K q)
  have hs : TensorQ.permAut swapFirstTwoPerm x = x :=
    TensorQ.toQ_eq_iff.2 (CWRawSymmetry.CWObj_permObj_swapFirstTwo K q)
  have hcc : TensorQ.permAut (cyclicPerm.trans cyclicPerm) x = x := by
    have h := (CWRawSymmetry.permObj_trans_iso_local cyclicPerm cyclicPerm (CWObj K q)).symm.trans
      ((TensorObj.permObj_isomorphic cyclicPerm
        (CWRawSymmetry.CWObj_permObj_cyclic K q)).trans
        (CWRawSymmetry.CWObj_permObj_cyclic K q))
    exact TensorQ.toQ_eq_iff.2 h
  have hf : TensorQ.toQ (StothersFourth.cwFourthObj K q) = x ^ 4 := by
    simp only [StothersFourth.cwFourthObj, TensorQ.toQ_kron]
    dsimp only [x]
    ring
  have hcyc : TensorQ.toQ (cyclicSymmetrization (StothersFourth.cwFourthObj K q)) =
      x ^ 12 := by
    rw [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron, TensorQ.toQ_kron]
    change TensorQ.toQ (StothersFourth.cwFourthObj K q) *
      (TensorQ.permAut cyclicPerm (TensorQ.toQ (StothersFourth.cwFourthObj K q)) *
        TensorQ.permAut (cyclicPerm.trans cyclicPerm)
          (TensorQ.toQ (StothersFourth.cwFourthObj K q))) = _
    rw [hf, map_pow, map_pow, hc, hcc]
    ring
  have hfull : TensorQ.toQ (sixSymmetrization (StothersFourth.cwFourthObj K q)) =
      x ^ 24 := by
    change TensorQ.toQ (cyclicSymmetrization (StothersFourth.cwFourthObj K q)) *
      TensorQ.permAut swapFirstTwoPerm
        (TensorQ.toQ (cyclicSymmetrization (StothersFourth.cwFourthObj K q))) = _
    rw [hcyc, map_pow, hs]
    ring
  apply TensorQ.toQ_eq_iff.1
  rw [TensorQ.toQ_kronPow, TensorQ.toQ_kronPow, hfull, pow_mul]

#print axioms solution
