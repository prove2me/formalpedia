-- Prove2me | Theorems.Thm_mme_bigAdd_fin_mul_grouped_restrict
-- name    : mme_bigAdd_fin_mul_grouped_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:04:26.931579+00:00
-- url     : https://prove2.me/theorems/05f29929-e486-432d-aaca-950987ad54ba
-- title:
--   Assembling fixed-group tensor restrictions into a flat direct sum
-- statement:
--   Let $X_{a,b}$ be tensors indexed by $a\in\operatorname{Fin}(k)$ and $b\in\operatorname{Fin}(g)$, and let $Y_a$ be a target for each fixed $a$. Suppose each grouped source direct sum restricts to its target,
--
--   $$
--   Y_a\leq\bigoplus_{b\in\operatorname{Fin}(g)}X_{a,b}.
--   $$
--
--   Then the direct sum of all $Y_a$ restricts from the flat direct sum of all $kg$ source tensors, where $\operatorname{Fin}(kg)$ is identified canonically with $\operatorname{Fin}(k)\times\operatorname{Fin}(g)$:
--
--   $$
--   \bigoplus_{a\in\operatorname{Fin}(k)}Y_a\leq\bigoplus_{r\in\operatorname{Fin}(kg)}X_{r_1,r_2}.
--   $$
--
--   This is the assembly step for the fixed-size multi-copy Hole-Lemma amplification in Corollary 5.11.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.3, Lemma 5.6 and Corollary 5.11 (grouping broken tensors and assembling their repaired outputs); https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_bigAdd_fin_mul_isomorphic_nested
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_bigAdd_fin_mul_grouped_restrict
    {K : Type u} [Field K] {d k g : ℕ}
    (X : Fin k → Fin g → TensorObj K d)
    (Y : Fin k → TensorObj K d)
    (hgroup : ∀ a, TensorObj.Restrict (Y a)
      (TensorObj.bigAdd (fun b : Fin g ↦ X a b))) :
    TensorObj.Restrict
      (TensorObj.bigAdd Y)
      (TensorObj.bigAdd (fun r : Fin (k * g) ↦
        X (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)) := by
  sorry
