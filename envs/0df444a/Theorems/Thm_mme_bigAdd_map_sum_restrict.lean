-- Prove2me | Theorems.Thm_mme_bigAdd_map_sum_restrict
-- name    : mme_bigAdd_map_sum_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T10:19:40.242377+00:00
-- url     : https://prove2.me/theorems/f2f34da7-08fc-4868-9c55-d781a07ba3fb
-- title:
--   Identification of a finite tensor direct sum is a restriction
-- statement:
--   Let $X_0,\ldots,X_{s-1}$ be order-$d$ tensors over a field $K$. For every summand $j$ and mode $i$, let $f_{j,i}$ be a linear map from the $i$-th mode space of $X_j$ to a common finite-dimensional space $W_i$. Then
--
--   $$
--   \sum_{j<s}\left(\bigotimes_{i<d} f_{j,i}\right)(X_j)
--   \quad\text{is a restriction of}\quad
--   \bigoplus_{j<s}X_j.
--   $$
--
--   This is the ordinary linear identification operation used when the Hole Lemma glues shuffled broken copies. A concrete application must separately prove that the displayed sum is exactly the desired repaired tensor; that conclusion is not assumed here.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, identification in Section 3.2 (printed p. 17) and its use in the proof of Lemma 5.6 (printed p. 49).

import Definitions.Def_mme_tensor_rank
open MME PiTensorProduct BigOperators
universe u

theorem mme_bigAdd_map_sum_restrict
    {K : Type u} [Field K] {d s : ℕ}
    (X : Fin s → TensorObj K d)
    {W : Fin d → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, Module.Finite K (W i)]
    (f : ∀ j i, (X j).V i →ₗ[K] W i) :
    TensorObj.Restrict
      ({ V := W
         t := ∑ j, PiTensorProduct.map (f j) (X j).t } : TensorObj K d)
      (TensorObj.bigAdd X) := by sorry
