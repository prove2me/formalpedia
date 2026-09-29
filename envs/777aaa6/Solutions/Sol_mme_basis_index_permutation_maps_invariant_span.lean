-- Prove2me | solution 1 for mme_basis_index_permutation_maps_invariant_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:26:03.70906+00:00
-- url     : https://prove2.me/submissions/5efd9751-c31a-4e77-903b-6ae43258a818

import Definitions.Def_mme_basis_index_permutation

open Module

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι : Type u} (b : Basis ι K V) (e : ι ≃ ι)
    (allowed : ι → Prop)
    (hinv : ∀ j, allowed (e j) ↔ allowed j) :
    Submodule.map
        (MME.DWZComponentRestriction.basisIndexPermEquiv b e).toLinearMap
        (Submodule.span K (b '' {j | allowed j})) =
      Submodule.span K (b '' {j | allowed j}) := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨e j, ?_,
      (MME.DWZComponentRestriction.basisIndexPermEquiv_apply_basis b e j).symm⟩
    exact (hinv j).2 hj
  · rintro ⟨j, hj, rfl⟩
    refine ⟨b (e.symm j), ⟨e.symm j, ?_, rfl⟩, ?_⟩
    · exact (hinv (e.symm j)).1 (by simpa using hj)
    · simp
