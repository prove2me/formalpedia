-- Prove2me | Theorems.Thm_mme_bigAdd_list_prefix_restrict
-- name    : mme_bigAdd_list_prefix_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:32:20.529807+00:00
-- url     : https://prove2.me/theorems/4bcf1c6b-81a7-463c-a5d2-099efd5c5606
-- title:
--   Selecting a literal list prefix of tensor direct-sum summands
-- statement:
--   For tensor objects indexed by an item list, the direct sum over a literal prefix is a restriction of the direct sum over the prefix followed by any remainder. This is the list-indexed adapter that lets the greedy Corollary-5.11 groups discard their final unused suffix while preserving the source tensor restriction.
-- source:
--   Finite direct-sum functoriality; used in Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Corollary 5.11; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_bigAdd_prefix_restrict

open MME BigOperators

universe u v

set_option autoImplicit false

theorem mme_bigAdd_list_prefix_restrict
    {K : Type u} [Field K] {d : ℕ} {Item : Type v}
    (hd : 1 < d) (X : Item → TensorObj K d)
    (pre remainder : List Item) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun i : Fin pre.length ↦ X (pre.get i)))
      (TensorObj.bigAdd (fun i : Fin (pre ++ remainder).length ↦
        X ((pre ++ remainder).get i))) := by
  sorry
