-- Prove2me | solution 1 for mme_bigAdd_cartesian_kron_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:31:52.706593+00:00
-- url     : https://prove2.me/submissions/9c856b05-9181-4106-87ef-df8bd94ed6a1

import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {d A B : ℕ}
    (X : Fin A → TensorObj K d) (Y : Fin B → TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun r : Fin (A * B) ↦
        TensorObj.kron
          (X (finProdFinEquiv.symm r).1)
          (Y (finProdFinEquiv.symm r).2)))
      (TensorObj.kron (TensorObj.bigAdd X) (TensorObj.bigAdd Y)) := by
  apply (TensorQ.toQ_eq_iff).mp
  rw [TensorQ.toQ_bigAdd, TensorQ.toQ_kron,
    TensorQ.toQ_bigAdd, TensorQ.toQ_bigAdd]
  simp_rw [TensorQ.toQ_kron]
  calc
    (∑ r : Fin (A * B),
        TensorQ.toQ (X (finProdFinEquiv.symm r).1) *
          TensorQ.toQ (Y (finProdFinEquiv.symm r).2)) =
      ∑ p : Fin A × Fin B,
        TensorQ.toQ (X p.1) * TensorQ.toQ (Y p.2) := by
          symm
          apply Fintype.sum_equiv finProdFinEquiv
          intro p
          simp
    _ = ∑ a : Fin A, ∑ b : Fin B,
        TensorQ.toQ (X a) * TensorQ.toQ (Y b) := by
          rw [Fintype.sum_prod_type]
    _ = (∑ a : Fin A, TensorQ.toQ (X a)) *
        (∑ b : Fin B, TensorQ.toQ (Y b)) := by
          symm
          rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]

