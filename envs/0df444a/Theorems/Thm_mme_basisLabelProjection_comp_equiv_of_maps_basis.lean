-- Prove2me | Theorems.Thm_mme_basisLabelProjection_comp_equiv_of_maps_basis
-- name    : mme_basisLabelProjection_comp_equiv_of_maps_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:36:14.768267+00:00
-- url     : https://prove2.me/theorems/9c4fe491-ee67-40c9-98da-0ad2ba929ab3
-- title:
--   Singleton basis projections commute with label-preserving equivalences
-- statement:
--   Let two finite-dimensional modules carry bases indexed by the same finite label set. If a linear equivalence sends every source basis vector to the target basis vector with the same label, then it commutes with projection onto any singleton basis label.
-- source:
--   Standard linear algebra: verification on a basis.

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module

universe u

set_option autoImplicit false

theorem mme_basisLabelProjection_comp_equiv_of_maps_basis
    {K : Type u} [Field K]
    {V V' : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V']
    {I : Type u} [Fintype I] [DecidableEq I]
    (b : Basis I K V) (b' : Basis I K V') (e : V ≃ₗ[K] V')
    (hbasis : ∀ a, e (b a) = b' a) (selected : I) :
    (MME.DWZComponentRestriction.basisLabelProjection
        b' id {selected}).comp e.toLinearMap =
      e.toLinearMap.comp
        (MME.DWZComponentRestriction.basisLabelProjection
          b id {selected}) := by
  sorry
