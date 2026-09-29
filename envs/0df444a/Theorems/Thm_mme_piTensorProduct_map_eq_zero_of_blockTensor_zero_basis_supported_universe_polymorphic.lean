-- Prove2me | Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_blockTensor_zero_basis_supported_universe_polymorphic
-- name    : mme_piTensorProduct_map_eq_zero_of_blockTensor_zero_basis_supported_universe_polymorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T23:06:47.674279+00:00
-- url     : https://prove2.me/theorems/e0ab8850-04f0-4144-ae28-4fbbd63a4c25
-- title:
--   Universe-polymorphic basis-supported factorization through a zero tensor block
-- statement:
--   Let a tensor over a field carry a finite type grading and a homogeneous basis in every mode. Choose one basis vector in each mode, and suppose each output map vanishes on all other basis vectors. If the grading block containing the selected tuple is zero, then the tensor obtained by applying all output maps is zero. The field, basis-label sets, and output spaces may inhabit independent universes.
-- source:
--   Standard multilinear algebra: homogeneous basis projections and tensor-product functoriality.

import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u v w

set_option autoImplicit false

theorem mme_piTensorProduct_map_eq_zero_of_blockTensor_zero_basis_supported_universe_polymorphic
    {K : Type u} [Field K] {d t : ℕ}
    {T : TensorObj K d}
    (G : T.TypeGrading t)
    {Index : Fin d → Type v}
    [∀ i, Fintype (Index i)] [∀ i, DecidableEq (Index i)]
    (b : ∀ i, Basis (Index i) K (T.V i))
    (grade : ∀ i, Index i → Fin t)
    (hhomogeneous : ∀ i x,
      b i x ∈ G.classOf i (grade i x))
    (selected : ∀ i, Index i)
    {W : Fin d → Type w}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (maps : ∀ i, T.V i →ₗ[K] W i)
    (hsupported : ∀ i x, x ≠ selected i → maps i (b i x) = 0)
    (hzero : G.blockTensor (fun i ↦ grade i (selected i)) = 0) :
    PiTensorProduct.map maps T.t = 0 := by
  sorry
