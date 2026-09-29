-- Prove2me | solution 1 for mme_basisLabelProjection_comp_equiv_of_maps_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:36:32.998749+00:00
-- url     : https://prove2.me/submissions/2e5f3c2b-5cd3-4215-b28b-cae39decd940

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
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
  apply b.ext
  intro a
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold MME.DWZComponentRestriction.basisLabelProjection
  rw [Module.Basis.constr_basis]
  simp only [id_eq, Finset.mem_singleton]
  by_cases ha : a = selected
  · rw [if_pos ha]
    have he : e.toLinearMap (b a) = b' a := hbasis a
    rw [he, Module.Basis.constr_basis]
    simp only [if_pos ha]
  · rw [if_neg ha, map_zero]
    have he : e.toLinearMap (b a) = b' a := hbasis a
    rw [he, Module.Basis.constr_basis]
    simp only [if_neg ha]
