-- Prove2me | solution 1 for mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:46:35.06999+00:00
-- url     : https://prove2.me/submissions/8b3d7f6c-9e0d-4cd1-b31c-67e0dbe96b54

import Theorems.Thm_mme_bigAdd_cartesian_kron_isomorphic
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_rank_bridge

open MME BigOperators
universe u
set_option autoImplicit false

namespace MME.CyclicMatrixDirectSum
variable {K : Type u} [Field K]

private theorem bigAdd_iso {q : ℕ} (X Y : Fin q → TensorObj K 3)
    (h : ∀ j, TensorObj.Isomorphic (X j) (Y j)) :
    TensorObj.Isomorphic (TensorObj.bigAdd X) (TensorObj.bigAdd Y) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_bigAdd, TensorQ.toQ_bigAdd]
  exact Finset.sum_congr rfl (fun j _ ↦ TensorQ.toQ_eq_iff.mpr (h j))

private theorem kron_iso {X X' Y Y' : TensorObj K 3}
    (hX : TensorObj.Isomorphic X X') (hY : TensorObj.Isomorphic Y Y') :
    TensorObj.Isomorphic (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_kron, TensorQ.toQ_kron,
    TensorQ.toQ_eq_iff.mpr hX, TensorQ.toQ_eq_iff.mpr hY]

private theorem perm_bigAdd (e : Equiv.Perm (Fin 3)) {q : ℕ}
    (X : Fin q → TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.permObj e (TensorObj.bigAdd X))
      (TensorObj.bigAdd (fun j ↦ TensorObj.permObj e (X j))) := by
  apply TensorQ.toQ_eq_iff.mp
  change TensorQ.permAut e (TensorQ.toQ (TensorObj.bigAdd X)) = _
  rw [TensorQ.toQ_bigAdd, TensorQ.toQ_bigAdd, map_sum]
  rfl

private theorem perm_twice (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm (TensorObj.permObj cyclicPerm T))
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T) := by
  have ht : (TensorObj.permObj cyclicPerm (TensorObj.permObj cyclicPerm T)).t =
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T).t :=
    PiTensorProduct.reindex_reindex cyclicPerm cyclicPerm T.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    exact (LinearMap.congr_fun (PiTensorProduct.map_id (R := K)
      (s := (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T).V)) _).trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    exact (LinearMap.congr_fun (PiTensorProduct.map_id (R := K)
      (s := (TensorObj.permObj cyclicPerm (TensorObj.permObj cyclicPerm T)).V)) _).trans ht

end MME.CyclicMatrixDirectSum

/-- Cyclic symmetrization distributes over all triples of matrix summands.
Equal input volumes give equal cubed volumes, without uniform dimensions. -/
theorem solution
    {K : Type u} [Field K] {q v : ℕ} (a b c : Fin q → ℕ)
    (hvol : ∀ j, a j * b j * c j = v) :
    ∃ (Q : ℕ) (A B C : Fin Q → ℕ), Q = q ^ 3 ∧
      TensorObj.Isomorphic
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        (cyclicSymmetrization (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))) ∧
      ∀ j, A j * B j * C j = v ^ 3 := by
  let X := fun j ↦ MMObj K (a j) (b j) (c j)
  let Y := fun j ↦ MMObj K (c j) (a j) (b j)
  let Z := fun j ↦ MMObj K (b j) (c j) (a j)
  let first := fun r : Fin (q * (q * q)) ↦ (finProdFinEquiv.symm r).1
  let second := fun r : Fin (q * (q * q)) ↦
    (finProdFinEquiv.symm (finProdFinEquiv.symm r).2).1
  let third := fun r : Fin (q * (q * q)) ↦
    (finProdFinEquiv.symm (finProdFinEquiv.symm r).2).2
  let A := fun r ↦ a (first r) * (c (second r) * b (third r))
  let B := fun r ↦ b (first r) * (a (second r) * c (third r))
  let C := fun r ↦ c (first r) * (b (second r) * a (third r))
  have hrot (a b c : Fin q → ℕ) : TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j))))
      (TensorObj.bigAdd (fun j ↦ MMObj K (c j) (a j) (b j))) :=
    (MME.CyclicMatrixDirectSum.perm_bigAdd _ _).trans
      (MME.CyclicMatrixDirectSum.bigAdd_iso _ _ (fun j ↦ MMObj_permObj_cyclic _ _ _))
  have hrot2 : TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (TensorObj.bigAdd X))
      (TensorObj.bigAdd Z) :=
    (MME.CyclicMatrixDirectSum.perm_twice _).symm.trans
      ((TensorObj.permObj_isomorphic cyclicPerm (hrot a b c)).trans (hrot c a b))
  let YZ := fun r : Fin (q * q) ↦ TensorObj.kron
    (Y (finProdFinEquiv.symm r).1) (Z (finProdFinEquiv.symm r).2)
  have hblocks : TensorObj.Isomorphic
      (TensorObj.bigAdd (fun r ↦ MMObj K (A r) (B r) (C r)))
      (TensorObj.bigAdd (fun r : Fin (q * (q * q)) ↦
        TensorObj.kron (X (first r)) (YZ (finProdFinEquiv.symm r).2))) := by
    apply MME.CyclicMatrixDirectSum.bigAdd_iso
    intro r
    exact ((MME.CyclicMatrixDirectSum.kron_iso (TensorObj.Isomorphic.refl _)
      (MMObj_kron_iso _ _ _ _ _ _)).trans (MMObj_kron_iso _ _ _ _ _ _)).symm
  refine ⟨q * (q * q), A, B, C, by ring, ?_, ?_⟩
  · rw [cyclicSymmetrization_eq_public_perm]
    exact hblocks.trans ((mme_bigAdd_cartesian_kron_isomorphic X YZ).trans
      ((MME.CyclicMatrixDirectSum.kron_iso (TensorObj.Isomorphic.refl _)
        (mme_bigAdd_cartesian_kron_isomorphic Y Z)).trans
        (MME.CyclicMatrixDirectSum.kron_iso (TensorObj.Isomorphic.refl _)
          (MME.CyclicMatrixDirectSum.kron_iso (hrot a b c).symm hrot2.symm))))
  · intro r
    change (a (first r) * (c (second r) * b (third r))) *
      (b (first r) * (a (second r) * c (third r))) *
      (c (first r) * (b (second r) * a (third r))) = v ^ 3
    calc
      _ = (a (first r) * b (first r) * c (first r)) *
          (a (second r) * b (second r) * c (second r)) *
          (a (third r) * b (third r) * c (third r)) := by ring
      _ = v ^ 3 := by rw [hvol, hvol, hvol]; ring
