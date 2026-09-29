-- Prove2me | Theorems.Thm_mme_piTensorProduct_map_injective_of_modewise_injective
-- name    : mme_piTensorProduct_map_injective_of_modewise_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:23:08.193025+00:00
-- url     : https://prove2.me/theorems/b730ee70-14a8-4755-96ec-c7397e255675
-- title:
--   Pi-tensor products preserve injective linear maps over fields
-- statement:
--   Let $(V_i)_{i\in I}$ and $(W_i)_{i\in I}$ be finite families of vector spaces over a field $K$. If every linear map $f_i:V_i\to W_i$ is injective, then their induced map on the Pi-tensor product is injective:
--
--   $$
--   \bigotimes_{i\in I} f_i:\bigotimes_{i\in I}V_i\longrightarrow\bigotimes_{i\in I}W_i.
--   $$
--
--   This provides a reusable cancellation principle for comparing tensors after embedding every mode into an ambient space. In particular, it lets one transfer equality back from the tensorized inclusions of graded block subspaces.
--
--   **Formalization Note** The index type is finite and the result includes the empty family.
-- source:
--   Standard multilinear algebra: over a field every injective linear map splits, and tensoring the resulting left inverses gives a left inverse of the tensor-product map. Used for the block-inclusion step surrounding Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 5.9; https://arxiv.org/abs/2210.10173

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace

open PiTensorProduct

universe u v

set_option autoImplicit false

theorem mme_piTensorProduct_map_injective_of_modewise_injective
    {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i)
    (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  sorry
