-- Prove2me | Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_blockTensor_zero_basis_supported
-- name    : mme_piTensorProduct_map_eq_zero_of_blockTensor_zero_basis_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T21:53:35.452292+00:00
-- url     : https://prove2.me/theorems/5d1d4d15-3bd8-4fdf-a3fe-cd09d8b42111
-- title:
--   Basis-supported mode maps factor through a zero grading block
-- statement:
--   Let a finite-dimensional tensor space carry a type grading and a homogeneous basis in each mode. Select one basis vector in each mode, and let each mode map vanish on all nonselected basis vectors. If the grading block containing the selected basis tuple is zero, then applying these maps to the tensor yields zero. The codomains and the images of the selected vectors are arbitrary.
-- source:
--   Standard multilinear algebra: homogeneous basis projections and functoriality of tensor products.

import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_piTensorProduct_map_eq_zero_of_blockTensor_zero_basis_supported
    {K : Type u} [Field K] {d t : ℕ}
    {T : TensorObj K d}
    (G : T.TypeGrading t)
    {Index : Fin d → Type u}
    [∀ i, Fintype (Index i)] [∀ i, DecidableEq (Index i)]
    (b : ∀ i, Basis (Index i) K (T.V i))
    (grade : ∀ i, Index i → Fin t)
    (hhomogeneous : ∀ i x,
      b i x ∈ G.classOf i (grade i x))
    (selected : ∀ i, Index i)
    {W : Fin d → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (maps : ∀ i, T.V i →ₗ[K] W i)
    (hsupported : ∀ i x, x ≠ selected i → maps i (b i x) = 0)
    (hzero : G.blockTensor (fun i ↦ grade i (selected i)) = 0) :
    PiTensorProduct.map maps T.t = 0 := by
  sorry
