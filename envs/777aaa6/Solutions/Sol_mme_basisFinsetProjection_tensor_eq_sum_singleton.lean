-- Prove2me | solution 1 for mme_basisFinsetProjection_tensor_eq_sum_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:29:37.897765+00:00
-- url     : https://prove2.me/submissions/4b39b9f7-5d53-4ccd-82a3-12fbb3a2e6c6

import Definitions.Def_mme_basis_z_allowed_projection

open BigOperators Finset
open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem basisFinsetProjection_eq_sum_singleton
    {K : Type u} [Field K]
    {ι β V : Type*} [AddCommMonoid V] [Module K V]
    [DecidableEq β]
    (b : Basis ι K V) (label : ι → β) (blocks : Finset β) :
    b.constr K (fun j ↦ if label j ∈ blocks then b j else 0) =
      ∑ block ∈ blocks,
        b.constr K (fun j ↦ if label j = block then b j else 0) := by
  apply b.ext
  intro j
  simp only [Module.Basis.constr_basis, LinearMap.sum_apply]
  change (if label j ∈ blocks then b j else 0) =
    ∑ block ∈ blocks, if label j = block then b j else 0
  by_cases hj : label j ∈ blocks
  · rw [if_pos hj]
    rw [Finset.sum_eq_single (label j)]
    · rw [if_pos rfl]
    · intro block hblock hne
      rw [if_neg (Ne.symm hne)]
    · intro hnot
      exact (hnot hj).elim
  · rw [if_neg hj]
    symm
    apply Finset.sum_eq_zero
    intro block hblock
    rw [if_neg]
    intro heq
    exact hj (heq ▸ hblock)

private theorem piTensorProduct_map_update_zero
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type*}
    [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin d) :
    PiTensorProduct.map (Function.update f i 0) = 0 := by
  have hzero := PiTensorProduct.map_update_smul
    f i (0 : K) (0 : V i →ₗ[K] W i)
  simpa only [zero_smul] using hzero

private theorem piTensorProduct_map_update_finset_sum
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type*}
    [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    {β : Type*} [DecidableEq β]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin d)
    (p : β → V i →ₗ[K] W i) (blocks : Finset β) :
    PiTensorProduct.map (Function.update f i (∑ block ∈ blocks, p block)) =
      ∑ block ∈ blocks,
        PiTensorProduct.map (Function.update f i (p block)) := by
  classical
  induction blocks using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact piTensorProduct_map_update_zero f i
  | @insert block blocks hnot ih =>
      rw [Finset.sum_insert hnot, Finset.sum_insert hnot,
        PiTensorProduct.map_update_add]
      rw [ih]

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) {ι β : Type u} [DecidableEq β]
    (b : Basis ι K (T.V 2)) (label : ι → β) (blocks : Finset β) :
    PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (b.constr K (fun j ↦ if label j ∈ blocks then b j else 0))) T.t =
      ∑ block ∈ blocks,
        PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (b.constr K (fun j ↦ if label j = block then b j else 0))) T.t := by
  rw [basisFinsetProjection_eq_sum_singleton b label blocks]
  rw [piTensorProduct_map_update_finset_sum]
  rw [LinearMap.sum_apply]
