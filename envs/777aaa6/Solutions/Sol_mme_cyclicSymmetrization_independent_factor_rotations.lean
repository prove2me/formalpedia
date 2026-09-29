-- Prove2me | solution 1 for mme_cyclicSymmetrization_independent_factor_rotations
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:53:10.561732+00:00
-- url     : https://prove2.me/submissions/e3ff1228-de12-4bfd-b2ce-9baf167ae9c8

import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME
universe u
set_option autoImplicit false

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


private theorem permObj_refl_iso
    {K : Type u} [Field K] (X : TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.permObj (Equiv.refl _) X) X := by
  have he : TensorObj.permObj (Equiv.refl _) X = X := by
    cases X
    simp only [TensorObj.permObj, PiTensorProduct.reindex_refl]
    rfl
  rw [he]
  exact TensorObj.Isomorphic.refl X

/-- A cyclic symmetrization is unchanged, up to tensor isomorphism, when
the two Kronecker factors are rotated independently in opposite directions. -/
theorem solution
    {K : Type u} [Field K] (X Y : TensorObj K 3) :
    TensorObj.Isomorphic
      (cyclicSymmetrization (TensorObj.kron
        (TensorObj.permObj cyclicPerm X)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) Y)))
      (cyclicSymmetrization (TensorObj.kron X Y)) := by
  let c2 := cyclicPerm.trans cyclicPerm
  have hcyc (Z : TensorObj K 3) :
      TensorQ.toQ (cyclicSymmetrization Z) = TensorQ.toQ Z *
        (TensorQ.permAut cyclicPerm (TensorQ.toQ Z) *
          TensorQ.permAut c2 (TensorQ.toQ Z)) := by
    rw [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron, TensorQ.toQ_kron]
    rfl
  have hcomp (Z : TensorObj K 3) (e e' : Equiv.Perm (Fin 3)) :
      TensorQ.permAut e' (TensorQ.permAut e (TensorQ.toQ Z)) =
        TensorQ.permAut (e.trans e') (TensorQ.toQ Z) :=
    TensorQ.toQ_eq_iff.mpr (permObj_trans_iso_pair e e' Z)
  have hc21 : c2.trans cyclicPerm = Equiv.refl _ := by
    ext i
    fin_cases i <;> rfl
  have hc12 : cyclicPerm.trans c2 = Equiv.refl _ := by
    ext i
    fin_cases i <;> rfl
  have hc22 : c2.trans c2 = cyclicPerm := by
    ext i
    fin_cases i <;> rfl
  have hid (Z : TensorObj K 3) :
      TensorQ.permAut (Equiv.refl _) (TensorQ.toQ Z) = TensorQ.toQ Z :=
    TensorQ.toQ_eq_iff.mpr (permObj_refl_iso Z)
  apply TensorQ.toQ_eq_iff.mp
  rw [hcyc, hcyc]
  simp only [TensorQ.toQ_kron, ← TensorQ.permAut_toQ, map_mul]
  rw [hcomp, hcomp, hcomp, hcomp]
  rw [hc21, hc12, hc22, hid, hid]
  ring

#print axioms solution
