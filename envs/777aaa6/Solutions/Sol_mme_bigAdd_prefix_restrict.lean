-- Prove2me | solution 1 for mme_bigAdd_prefix_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:50:53.349864+00:00
-- url     : https://prove2.me/submissions/0a591302-8a76-411e-93ab-9b72d69e171d

import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {d k n : ℕ}
    (hd : 1 < d) (hkn : k ≤ n) (X : Fin n → TensorObj K d) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun i : Fin k ↦ X (Fin.castLE hkn i)))
      (TensorObj.bigAdd X) := by
  rw [← TensorQ.le_toQ]
  rw [TensorQ.toQ_bigAdd, TensorQ.toQ_bigAdd]
  let e : Fin (k + (n - k)) ≃ Fin n :=
    finCongr (Nat.add_sub_of_le hkn)
  let tail : TensorQ K d :=
    ∑ i : Fin (n - k), TensorQ.toQ (X (e (Fin.natAdd k i)))
  have heprefix (i : Fin k) :
      e (Fin.castAdd (n - k) i) = Fin.castLE hkn i := by
    ext
    rfl
  have hsplit :
      (∑ i : Fin n, TensorQ.toQ (X i)) =
        (∑ i : Fin k, TensorQ.toQ (X (Fin.castLE hkn i))) + tail := by
    calc
      (∑ i : Fin n, TensorQ.toQ (X i)) =
          ∑ i : Fin (k + (n - k)), TensorQ.toQ (X (e i)) :=
        (Equiv.sum_comp e (fun i : Fin n ↦ TensorQ.toQ (X i))).symm
      _ = (∑ i : Fin k,
              TensorQ.toQ (X (e (Fin.castAdd (n - k) i)))) + tail := by
        simpa only [tail] using
          Fin.sum_univ_add (fun i : Fin (k + (n - k)) ↦
            TensorQ.toQ (X (e i)))
      _ = (∑ i : Fin k,
              TensorQ.toQ (X (Fin.castLE hkn i))) + tail := by
        simp_rw [heprefix]
  rw [hsplit]
  let P := TensorQ.tensorStrassen K d hd
  have hzero : P.le 0 tail := P.zero_le tail
  have hadd := P.add_right 0 tail hzero
    (∑ i : Fin k, TensorQ.toQ (X (Fin.castLE hkn i)))
  simpa only [zero_add, add_comm] using hadd
