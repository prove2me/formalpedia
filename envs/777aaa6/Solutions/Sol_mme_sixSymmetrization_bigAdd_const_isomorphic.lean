-- Prove2me | solution 1 for mme_sixSymmetrization_bigAdd_const_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:12:13.038387+00:00
-- url     : https://prove2.me/submissions/af5fdf14-c8fb-4d34-b3ac-bf39fea252e4

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

namespace SixSymmetrizationBigAddConstSolution

theorem toQ_bigAdd_const
    {K : Type u} [Field K]
    (T : TensorObj K 3) (k : ℕ) :
    TensorQ.toQ (TensorObj.bigAdd (fun _ : Fin k => T)) =
      (k : TensorQ K 3) * TensorQ.toQ T := by
  rw [TensorQ.toQ_bigAdd, Finset.sum_const, Finset.card_fin]
  rw [nsmul_eq_mul', mul_comm]

theorem toQ_sixSymmetrization
    {K : Type u} [Field K]
    (T : TensorObj K 3) :
    TensorQ.toQ (sixSymmetrization T) =
      (TensorQ.toQ T *
          (TensorQ.permAut cyclicPerm (TensorQ.toQ T) *
            TensorQ.permAut (cyclicPerm.trans cyclicPerm)
              (TensorQ.toQ T))) *
        TensorQ.permAut swapFirstTwoPerm
          (TensorQ.toQ T *
            (TensorQ.permAut cyclicPerm (TensorQ.toQ T) *
              TensorQ.permAut (cyclicPerm.trans cyclicPerm)
                (TensorQ.toQ T))) := by
  unfold sixSymmetrization
  rw [TensorQ.toQ_kron]
  rw [cyclicSymmetrization_eq_public_perm]
  simp only [TensorQ.toQ_kron, ← TensorQ.permAut_toQ, map_mul]

end SixSymmetrizationBigAddConstSolution

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (k : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization
        (TensorObj.bigAdd (fun _ : Fin k => T)))
      (TensorObj.bigAdd
        (fun _ : Fin (k ^ (6 : ℕ)) => sixSymmetrization T)) := by
  apply (TensorQ.toQ_eq_iff).1
  rw [SixSymmetrizationBigAddConstSolution.toQ_sixSymmetrization]
  rw [SixSymmetrizationBigAddConstSolution.toQ_bigAdd_const]
  rw [SixSymmetrizationBigAddConstSolution.toQ_bigAdd_const]
  rw [SixSymmetrizationBigAddConstSolution.toQ_sixSymmetrization]
  simp only [map_mul, map_natCast]
  rw [Nat.cast_pow]
  ring
