-- Prove2me | Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
-- name    : mme_tensor_family_direct_sum_restrict_of_mixed_maps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:39:08.567496+00:00
-- url     : https://prove2.me/theorems/bffe11bd-ba8c-4bdf-9f07-9bb4565df5f2
-- title:
--   Mixed-term vanishing assembles arbitrary tensor targets as a direct-sum restriction
-- statement:
--   Let $S$ be an order-three tensor and let $B_0,\ldots,B_{k-1}$ be arbitrary order-three target tensors. For every target $B_j$ and tensor mode $i$, choose a linear map $f_{j,i}$ from the $i$-th mode space of $S$ to that of $B_j$. Suppose the three maps with one common index $j$ send $S$ exactly to $B_j$, while every nonconstant mixed choice $(j_0,j_1,j_2)$ sends $S$ to zero. Then the direct sum of all targets is a restriction of the source:
--
--   $$
--   \bigoplus_{j<k} B_j \;\leq\; S.
--   $$
--
--   The targets are otherwise unrestricted and may themselves retain sums of many components with shared mode spaces. This is the appropriate assembly interface for asymmetric-hashing constructions in which internal fine blocks must not be treated as independent direct-sum summands.
-- source:
--   Standard multilinear direct-sum extraction; used for the source-faithful tensor-semantic packaging after Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 2 and Section 5; https://arxiv.org/abs/2210.10173

import Mathlib.LinearAlgebra.PiTensorProduct
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_tensor_rank

open MME PiTensorProduct BigOperators

universe u

set_option autoImplicit false

theorem mme_tensor_family_direct_sum_restrict_of_mixed_maps
    {K : Type u} [Field K]
    (S : TensorObj K 3) {k : ℕ}
    (B : Fin k → TensorObj K 3)
    (f : ∀ j : Fin k, ∀ i : Fin 3, S.V i →ₗ[K] (B j).V i)
    (hDiagonal : ∀ j : Fin k,
      PiTensorProduct.map (f j) S.t = (B j).t)
    (hMixedZero : ∀ js : Fin 3 → Fin k,
      (∀ j : Fin k, js ≠ fun _ ↦ j) →
      PiTensorProduct.map (fun i ↦ f (js i) i) S.t = 0) :
    TensorObj.Restrict (TensorObj.bigAdd B) S := by
  sorry
