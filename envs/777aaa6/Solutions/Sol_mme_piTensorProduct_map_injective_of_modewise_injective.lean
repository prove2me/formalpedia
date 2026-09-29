-- Prove2me | solution 1 for mme_piTensorProduct_map_injective_of_modewise_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:26:46.148796+00:00
-- url     : https://prove2.me/submissions/24b02506-69d9-48cb-8f89-9bdcb9350caa

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace

open PiTensorProduct

universe u v

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i)
    (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  have hker : ∀ i, LinearMap.ker (f i) = ⊥ :=
    fun i ↦ LinearMap.ker_eq_bot.mpr (hf i)
  choose g hg using fun i ↦
    (f i).exists_leftInverse_of_injective (hker i)
  apply (show Function.LeftInverse (PiTensorProduct.map g)
      (PiTensorProduct.map f) from ?_).injective
  intro x
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have hgf : (fun i ↦ (g i).comp (f i)) =
      (fun i ↦ (LinearMap.id : V i →ₗ[K] V i)) := by
    funext i
    exact hg i
  rw [hgf, PiTensorProduct.map_id]
  rfl
