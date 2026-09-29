-- Prove2me | Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
-- name    : mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:53:27.764447+00:00
-- url     : https://prove2.me/theorems/cf0a604a-19c8-4c0b-8db8-f67eda73c2db
-- title:
--   Selected singleton slices control an arbitrary tensor mode
-- statement:
--   Let $S$ and $U$ be order-$d$ tensors and choose any mode $r$. Suppose the mode-$r$ map factors through a finite based space $Z$ and a selector that kills every basis vector outside a predicate $P$. If the mapped tensor vanishes after restricting mode $r$ to each singleton basis vector satisfying $P$, then the complete mapped tensor vanishes. All other mode maps and the chosen mode $r$ are arbitrary. This is the mode-symmetric finite basis expansion needed to analyze simultaneous X-, Y-, and Z-word filters.

import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_tensor

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
    {K : Type u} [Field K] {d : ℕ}
    {S U : TensorObj K d} {Z I : Type u}
    [AddCommGroup Z] [Module K Z]
    [Fintype I] [DecidableEq I]
    (slot : Fin d)
    (b : Basis I K Z) (allowed : I → Prop)
    [DecidablePred allowed]
    (pre : S.V slot →ₗ[K] Z) (select : Z →ₗ[K] U.V slot)
    (maps : ∀ i : Fin d, S.V i →ₗ[K] U.V i)
    (hslot : maps slot = select.comp pre)
    (hdisallowed : ∀ j : I, ¬ allowed j → select (b j) = 0)
    (hzero : ∀ j : I, allowed j →
      let singleton : Z →ₗ[K] Z :=
        MME.DWZComponentRestriction.basisLabelProjection b id {j}
      PiTensorProduct.map
        (Function.update maps slot
          ((select.comp singleton).comp pre)) S.t = 0) :
    PiTensorProduct.map maps S.t = 0 := by
  sorry
