-- Prove2me | solution 1 for mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:21:50.069424+00:00
-- url     : https://prove2.me/submissions/22e9c159-4fc3-4cec-820b-51f705c73211

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_duality

open MME

universe u


theorem solution
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    (X : TensorObj K d) (N : ℕ) (hN : 1 ≤ N) :
    tensorAsymptoticRank (X.kronPow N) = tensorAsymptoticRank X ^ N := by
  calc
    tensorAsymptoticRank (X.kronPow N) =
        StrassenPreorder.asymptoticRank (TensorQ.tensorStrassen K d hd)
          (TensorQ.toQ (X.kronPow N)) :=
      TensorQ.tensorAsymptoticRank_eq hd (X.kronPow N)
    _ = StrassenPreorder.asymptoticRank (TensorQ.tensorStrassen K d hd)
          ((TensorQ.toQ X) ^ N) := by rw [TensorQ.toQ_kronPow]
    _ = (StrassenPreorder.asymptoticRank (TensorQ.tensorStrassen K d hd)
          (TensorQ.toQ X)) ^ N :=
      StrassenPreorder.asymptoticRank_pow
        (TensorQ.tensorStrassen K d hd) (TensorQ.toQ X) N hN
    _ = tensorAsymptoticRank X ^ N := by
      rw [TensorQ.tensorAsymptoticRank_eq hd X]
