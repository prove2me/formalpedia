-- Prove2me | Theorems.Thm_mme_piTensorProduct_map_basis_filter_eq_of_rejected_singletons_zero
-- name    : mme_piTensorProduct_map_basis_filter_eq_of_rejected_singletons_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T21:23:47.59956+00:00
-- url     : https://prove2.me/theorems/6e4afb12-3687-403e-be81-190e0b0ccad5
-- title:
--   Rejected singleton vanishing permits a basis filter
-- statement:
--   Let a finite basis of one mode of a tensor be split into allowed and rejected labels. If the mapped tensor vanishes after restricting that mode to each rejected singleton basis vector, then inserting the diagonal projector onto all allowed labels leaves the mapped tensor unchanged. The theorem works at any mode and with arbitrary maps on all other modes.

import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_piTensorProduct_map_basis_filter_eq_of_rejected_singletons_zero
    {K : Type u} [Field K] {d : ℕ}
    {S U : TensorObj K d} {I : Type u}
    [Fintype I] [DecidableEq I]
    (slot : Fin d) (b : Basis I K (S.V slot))
    (allowed : I → Prop) [DecidablePred allowed]
    (maps : ∀ i : Fin d, S.V i →ₗ[K] U.V i)
    (hzero : ∀ j : I, ¬ allowed j →
      let singleton : S.V slot →ₗ[K] S.V slot :=
        MME.DWZComponentRestriction.basisLabelProjection b id {j}
      PiTensorProduct.map
        (Function.update maps slot ((maps slot).comp singleton)) S.t = 0) :
    let keep : S.V slot →ₗ[K] S.V slot :=
      MME.DWZComponentRestriction.basisLabelProjection b id
        (Finset.univ.filter allowed)
    PiTensorProduct.map
        (Function.update maps slot ((maps slot).comp keep)) S.t =
      PiTensorProduct.map maps S.t := by
  sorry
