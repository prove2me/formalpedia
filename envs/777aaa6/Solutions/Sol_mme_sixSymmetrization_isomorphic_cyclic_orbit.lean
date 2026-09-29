-- Prove2me | solution 1 for mme_sixSymmetrization_isomorphic_cyclic_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:44:39.247291+00:00
-- url     : https://prove2.me/submissions/66948a2c-0678-4cc0-8c57-e41fae72d681

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false

namespace MME

private theorem permObj_trans_iso_pair
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

private theorem permAut_refl_toQ
    {K : Type u} [Field K] {d : ℕ} (T : TensorObj K d) :
    TensorQ.permAut (Equiv.refl (Fin d)) (TensorQ.toQ T) =
      TensorQ.toQ T := by
  change TensorQ.toQ (TensorObj.permObj (Equiv.refl (Fin d)) T) =
    TensorQ.toQ T
  apply TensorQ.toQ_eq_iff.mpr
  have ht : (TensorObj.permObj (Equiv.refl (Fin d)) T).t = T.t := by
    change (PiTensorProduct.reindex K T.V (Equiv.refl (Fin d))) T.t = T.t
    rw [PiTensorProduct.reindex_refl]
    rfl
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id (R := K) (s := T.V)) T.t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id (R := K) (s := T.V))
      ((TensorObj.permObj (Equiv.refl (Fin d)) T).t)
    exact hmap.trans ht

private theorem cyclicSymmetrization_cyclic_toQ
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorQ.toQ
        (cyclicSymmetrization (TensorObj.permObj cyclicPerm T)) =
      TensorQ.toQ (cyclicSymmetrization T) := by
  let c2 : Equiv.Perm (Fin 3) := cyclicPerm.trans cyclicPerm
  let q : TensorQ K 3 := TensorQ.toQ T
  have hcomp (e e' : Equiv.Perm (Fin 3)) :
      TensorQ.permAut e' (TensorQ.permAut e q) =
        TensorQ.permAut (e.trans e') q := by
    change TensorQ.toQ (TensorObj.permObj e'
        (TensorObj.permObj e T)) =
      TensorQ.toQ (TensorObj.permObj (e.trans e') T)
    exact TensorQ.toQ_eq_iff.mpr (permObj_trans_iso_pair e e' T)
  have hc3 : cyclicPerm.trans c2 = Equiv.refl (Fin 3) := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  rw [cyclicSymmetrization_eq_public_perm,
    cyclicSymmetrization_eq_public_perm]
  simp only [TensorQ.toQ_kron, ← TensorQ.permAut_toQ]
  change
    TensorQ.permAut cyclicPerm q *
        (TensorQ.permAut cyclicPerm (TensorQ.permAut cyclicPerm q) *
          TensorQ.permAut c2 (TensorQ.permAut cyclicPerm q)) =
      q * (TensorQ.permAut cyclicPerm q * TensorQ.permAut c2 q)
  rw [hcomp cyclicPerm cyclicPerm, hcomp cyclicPerm c2, hc3]
  rw [permAut_refl_toQ T]
  change
    TensorQ.permAut cyclicPerm q *
        (TensorQ.permAut c2 q * q) =
      q * (TensorQ.permAut cyclicPerm q * TensorQ.permAut c2 q)
  ring

private theorem cyclicSymmetrization_cyclicSq_toQ
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorQ.toQ
        (cyclicSymmetrization
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T)) =
      TensorQ.toQ (cyclicSymmetrization T) := by
  let c2 : Equiv.Perm (Fin 3) := cyclicPerm.trans cyclicPerm
  let q : TensorQ K 3 := TensorQ.toQ T
  have hcomp (e e' : Equiv.Perm (Fin 3)) :
      TensorQ.permAut e' (TensorQ.permAut e q) =
        TensorQ.permAut (e.trans e') q := by
    change TensorQ.toQ (TensorObj.permObj e'
        (TensorObj.permObj e T)) =
      TensorQ.toQ (TensorObj.permObj (e.trans e') T)
    exact TensorQ.toQ_eq_iff.mpr (permObj_trans_iso_pair e e' T)
  have hc3 : c2.trans cyclicPerm = Equiv.refl (Fin 3) := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have hc4 : c2.trans c2 = cyclicPerm := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  rw [cyclicSymmetrization_eq_public_perm,
    cyclicSymmetrization_eq_public_perm]
  simp only [TensorQ.toQ_kron, ← TensorQ.permAut_toQ]
  change
    TensorQ.permAut c2 q *
        (TensorQ.permAut cyclicPerm (TensorQ.permAut c2 q) *
          TensorQ.permAut c2 (TensorQ.permAut c2 q)) =
      q * (TensorQ.permAut cyclicPerm q * TensorQ.permAut c2 q)
  rw [hcomp c2 cyclicPerm, hcomp c2 c2, hc3, hc4]
  rw [permAut_refl_toQ T]
  change
    TensorQ.permAut c2 q *
        (q * TensorQ.permAut cyclicPerm q) =
      q * (TensorQ.permAut cyclicPerm q * TensorQ.permAut c2 q)
  ring

private theorem sixSymmetrization_isomorphic_permObj_cyclic
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (sixSymmetrization (TensorObj.permObj cyclicPerm T))
      (sixSymmetrization T) := by
  apply TensorQ.toQ_eq_iff.mp
  change
    TensorQ.toQ
        (TensorObj.kron
          (cyclicSymmetrization (TensorObj.permObj cyclicPerm T))
          (TensorObj.permObj swapFirstTwoPerm
            (cyclicSymmetrization (TensorObj.permObj cyclicPerm T)))) =
      TensorQ.toQ
        (TensorObj.kron (cyclicSymmetrization T)
          (TensorObj.permObj swapFirstTwoPerm
            (cyclicSymmetrization T)))
  simp only [TensorQ.toQ_kron, ← TensorQ.permAut_toQ]
  rw [cyclicSymmetrization_cyclic_toQ]

private theorem sixSymmetrization_isomorphic_permObj_cyclic_sq
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (sixSymmetrization
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T))
      (sixSymmetrization T) := by
  apply TensorQ.toQ_eq_iff.mp
  change
    TensorQ.toQ
        (TensorObj.kron
          (cyclicSymmetrization
            (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T))
          (TensorObj.permObj swapFirstTwoPerm
            (cyclicSymmetrization
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T)))) =
      TensorQ.toQ
        (TensorObj.kron (cyclicSymmetrization T)
          (TensorObj.permObj swapFirstTwoPerm
            (cyclicSymmetrization T)))
  simp only [TensorQ.toQ_kron, ← TensorQ.permAut_toQ]
  rw [cyclicSymmetrization_cyclicSq_toQ]

end MME

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic
        (sixSymmetrization (TensorObj.permObj cyclicPerm T))
        (sixSymmetrization T) ∧
      TensorObj.Isomorphic
        (sixSymmetrization
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T))
        (sixSymmetrization T) := by
  exact ⟨MME.sixSymmetrization_isomorphic_permObj_cyclic T,
    MME.sixSymmetrization_isomorphic_permObj_cyclic_sq T⟩
