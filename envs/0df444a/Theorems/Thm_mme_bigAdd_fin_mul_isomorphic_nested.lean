-- Prove2me | Theorems.Thm_mme_bigAdd_fin_mul_isomorphic_nested
-- name    : mme_bigAdd_fin_mul_isomorphic_nested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:38:49.906569+00:00
-- url     : https://prove2.me/theorems/7ab11a30-cafd-4a03-bfb2-fb12567d063a
-- title:
--   Regrouping a product-indexed finite tensor direct sum
-- statement:
--   Let $X_{a,b}$ be a finite family of tensors indexed by $a\in\operatorname{Fin}(k)$ and $b\in\operatorname{Fin}(g)$. Under the canonical equivalence $\operatorname{Fin}(kg)\cong\operatorname{Fin}(k)\times\operatorname{Fin}(g)$, the flat direct sum and the corresponding iterated direct sum are isomorphic:
--
--   $$
--   \bigoplus_{r\in\operatorname{Fin}(kg)} X_{r_1,r_2}
--   \cong
--   \bigoplus_{a\in\operatorname{Fin}(k)}\bigoplus_{b\in\operatorname{Fin}(g)}X_{a,b}.
--   $$
--
--   This provides the direct-sum regrouping used to amplify the DWZ Hole Lemma from one repaired group to many complete copies.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.3, Lemma 5.6 and Corollary 5.11 (grouping broken tensors before applying the Hole Lemma); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_bigAdd_fin_mul_isomorphic_nested
    {K : Type u} [Field K] {d k g : ℕ}
    (X : Fin k → Fin g → TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun r : Fin (k * g) ↦
        X (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2))
      (TensorObj.bigAdd (fun a : Fin k ↦
        TensorObj.bigAdd (fun b : Fin g ↦ X a b))) := by
  sorry
