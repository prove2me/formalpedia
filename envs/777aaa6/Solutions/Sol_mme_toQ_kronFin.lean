-- Prove2me | solution 1 for mme_toQ_kronFin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:39:46.703794+00:00
-- url     : https://prove2.me/submissions/a5a99f2c-2c81-473a-bec9-22cea3dbe0c8

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_rank_bridge

open MME BigOperators

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K] {d n : ℕ}
    (f : Fin n → TensorObj K d) :
    TensorQ.toQ (TensorObj.kronFin n f) =
      ∏ i, TensorQ.toQ (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [TensorObj.kronFin, TensorQ.toQ_kron,
        Fin.prod_univ_succ]
      exact congrArg (TensorQ.toQ (f 0) * ·)
        (ih (fun i => f i.succ))
