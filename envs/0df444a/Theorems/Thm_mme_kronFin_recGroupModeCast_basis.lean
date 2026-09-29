-- Prove2me | Theorems.Thm_mme_kronFin_recGroupModeCast_basis
-- name    : mme_kronFin_recGroupModeCast_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:47:11.042128+00:00
-- url     : https://prove2.me/theorems/275b42c4-9276-46c6-98ee-c10deff4d2de
-- title:
--   Consecutive-group mode casts preserve the exact dependent basis vector
-- statement:
--   For a family of tensors partitioned into consecutive fibers, fix a flat recursion position $r$ and let $s$ be its group label. The canonical equality between the tensor in group $s$ and the tensor stored at $r$ induces a mode-space cast. Simultaneously transport a basis index $x$ along the corresponding equality of dependent index types. The cast sends the group basis vector $b_s(x)$ exactly to the recursion-aligned flat basis vector at the transported index.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.5 (regrouping component powers and their word coordinates), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_rec_group_position_equiv_data

open MME Module

universe u

set_option autoImplicit false

theorem mme_kronFin_recGroupModeCast_basis
    {K : Type u} [Field K] {d k : ℕ} (count : Fin k → ℕ)
    (X : Fin k → TensorObj K d) (i : Fin d)
    (index : Fin k → Type u)
    (b : ∀ s, Basis (index s) K ((X s).V i))
    (r : Fin (TensorObj.recGroupLength k count))
    (x : index (TensorObj.recGroupPositionEquiv k count r).1) :
    let hX : X (TensorObj.recGroupPositionEquiv k count r).1 =
        TensorObj.recGroupFamily k count X r :=
      (TensorObj.recGroupFamily_at_position k count X r).symm
    let hIndex : index (TensorObj.recGroupPositionEquiv k count r).1 =
        TensorObj.recGroupFamily k count index r :=
      (TensorObj.recGroupFamily_at_position k count index r).symm
    LinearEquiv.cast (R := K)
        (M := fun U : TensorObj K d ↦ U.V i) hX (b _ x) =
      TensorObj.recGroupBasisFamily k count X i index b r
        (hIndex ▸ x) := by
  sorry
