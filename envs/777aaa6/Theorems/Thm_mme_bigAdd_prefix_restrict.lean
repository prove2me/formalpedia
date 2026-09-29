-- Prove2me | Theorems.Thm_mme_bigAdd_prefix_restrict
-- name    : mme_bigAdd_prefix_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:47:37.019564+00:00
-- url     : https://prove2.me/theorems/6cb92a74-0ef8-47e0-a8f1-616e4a0a1f28
-- title:
--   A prefix of a finite tensor direct sum is obtained by restriction
-- statement:
--   For any finite family of order-$d$ tensors with $d ≥ 2$, and any $k ≤ n$, the direct sum of the first $k$ tensors is a restriction of the direct sum of all $n$ tensors. Equivalently, one may discard an arbitrary tail of a direct sum by variable zeroing. This supplies the exact prefix-selection operation needed when a retained family is divided into fixed-size Hole-Lemma repair groups and its final incomplete group is discarded.
-- source:
--   Elementary tensor direct-sum zeroing used in the finite implementation of Duan--Wu--Zhou Corollary 5.11, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.3 and Equation (24), printed pp. 48--58; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_bigAdd_prefix_restrict
    {K : Type u} [Field K] {d k n : ℕ}
    (hd : 1 < d) (hkn : k ≤ n) (X : Fin n → TensorObj K d) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun i : Fin k ↦ X (Fin.castLE hkn i)))
      (TensorObj.bigAdd X) := by
  sorry
