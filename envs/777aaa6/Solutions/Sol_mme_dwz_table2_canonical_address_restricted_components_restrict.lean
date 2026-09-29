-- Prove2me | solution 1 for mme_dwz_table2_canonical_address_restricted_components_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:37:50.69097+00:00
-- url     : https://prove2.me/submissions/96e59dac-614a-4e31-b0c8-0255da9c025b

import Theorems.Thm_mme_dwz_table2_canonical_address_block_component_power_iso
import Definitions.Def_mme_rank_bridge

open MME
open MME.DWZSquare

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {N m : ℕ}
    (word : Fin N → Fin 15)
    (hword : ∀ s : Fin 15,
      Fintype.card {r : Fin N // word r = s} =
        MME.DWZTable2Counts.component s * m)
    (selected : Fin 15 → TensorObj K 3)
    (hselected : ∀ s : Fin 15,
      TensorObj.Restrict (selected s)
        (((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType (shapeX s) (shapeY s) (shapeZ s))).kronPow
            (MME.DWZTable2Counts.component s * m))) :
    let address : Fin 3 → Fin N → Fin 5 := fun i r ↦
      cwSquareBlockType
        (shapeX (word r)) (shapeY (word r)) (shapeZ (word r)) i
    TensorObj.Restrict
      (TensorObj.kronFin 15 selected)
      (gradedAddressBlock (cwSquareCanonicalGrading K 6) address) := by
  classical
  dsimp only
  have hkron : ∀ (n : ℕ) (X Y : Fin n → TensorObj K 3),
      (∀ i, TensorObj.Restrict (X i) (Y i)) →
      TensorObj.Restrict (TensorObj.kronFin n X)
        (TensorObj.kronFin n Y) := by
    intro n
    induction n with
    | zero =>
        intro X Y h
        exact TensorObj.Restrict.refl _
    | succ n ih =>
        intro X Y h
        change TensorObj.Restrict
          (TensorObj.kron (X 0)
            (TensorObj.kronFin n (fun i ↦ X i.succ)))
          (TensorObj.kron (Y 0)
            (TensorObj.kronFin n (fun i ↦ Y i.succ)))
        rw [← TensorQ.le_toQ]
        let P := TensorQ.tensorStrassen K 3 (by omega)
        have hx : P.le (TensorQ.toQ (X 0)) (TensorQ.toQ (Y 0)) := h 0
        have hy : P.le
            (TensorQ.toQ (TensorObj.kronFin n (fun i ↦ X i.succ)))
            (TensorQ.toQ (TensorObj.kronFin n (fun i ↦ Y i.succ))) :=
          ih (fun i ↦ X i.succ) (fun i ↦ Y i.succ) (fun i ↦ h i.succ)
        have hleft : P.le
            (TensorQ.toQ (X 0) *
              TensorQ.toQ (TensorObj.kronFin n (fun i ↦ X i.succ)))
            (TensorQ.toQ (Y 0) *
              TensorQ.toQ (TensorObj.kronFin n (fun i ↦ X i.succ))) :=
          P.mul_right _ _ hx _
        have hright : P.le
            (TensorQ.toQ (Y 0) *
              TensorQ.toQ (TensorObj.kronFin n (fun i ↦ X i.succ)))
            (TensorQ.toQ (Y 0) *
              TensorQ.toQ (TensorObj.kronFin n (fun i ↦ Y i.succ))) := by
          simpa only [mul_comm] using
            P.mul_right _ _ hy (TensorQ.toQ (Y 0))
        exact P.le_trans _ _ _ hleft hright
  have hcomponents : TensorObj.Restrict
      (TensorObj.kronFin 15 selected)
      (TensorObj.kronFin 15 (fun s ↦
        (((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType (shapeX s) (shapeY s) (shapeZ s))).kronPow
            (MME.DWZTable2Counts.component s * m)))) :=
    hkron 15 selected _ hselected
  have hiso := mme_dwz_table2_canonical_address_block_component_power_iso
    (K := K) word hword
  exact TensorObj.Restrict.trans hcomponents hiso.2
