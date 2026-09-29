-- Prove2me | Theorems.Thm_mme_dwz_restricted_component_Z_position_shuffle
-- name    : mme_dwz_restricted_component_Z_position_shuffle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:39:21.601267+00:00
-- url     : https://prove2.me/theorems/d8889afe-a4fb-4f9d-aba8-90708cb1b84a
-- title:
--   Position shuffling acts on a restricted Table-2 component Z mode
-- statement:
--   Fix a Table-2 component and its source-faithful restricted power, whose $Z$ mode is the span of exactly the available canonical words. Every permutation of the repeated component positions induces a linear automorphism of this selected $Z$ space. For each available word $w$, the automorphism sends its canonical basis vector to the canonical basis vector indexed by the reindexed word $w\circ e$.
--
--   This is the projected-$Z$ linear realization of Claims 5.8--5.9: the shuffle preserves the actual retained mode space, not merely the number of available words. The theorem includes the zero-scale case.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.4 and Claims 5.8--5.9, PDF pp. 48--50 / printed pp. 47--49; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_basis_index_permutation
import Theorems.Thm_mme_basis_index_permutation_maps_invariant_span
import Theorems.Thm_mme_dwz_component_word_allowed_reindex_iff
import Theorems.Thm_mme_dwz_table2_component_projection_certificate

open MME Module

universe u

set_option autoImplicit false

theorem mme_dwz_restricted_component_Z_position_shuffle
    {K : Type u} [Field K]
    (s : Fin 15) (m : ℕ)
    (e : Equiv.Perm
      (Fin (MME.DWZTable2Counts.component s * m))) :
    ∃ E :
        (MME.DWZComponentRestriction.restrictedComponentPower K s m).V 2 ≃ₗ[K]
          (MME.DWZComponentRestriction.restrictedComponentPower K s m).V 2,
      ∀ (w : MME.DWZComponentRestriction.PowIndex
          (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
            (MME.DWZSquare.shapeZ s))
          (MME.DWZTable2Counts.component s * m))
        (hw : MME.DWZComponentRestriction.componentWordAllowed s m w),
        E ⟨MME.DWZComponentRestriction.componentPowerZBasis K s m w, by
            rw [(mme_dwz_table2_component_projection_certificate
              (K := K) s m).2.2.2]
            exact Submodule.subset_span ⟨w, hw, rfl⟩⟩ =
          ⟨MME.DWZComponentRestriction.componentPowerZBasis K s m
              (MME.DWZComponentRestriction.PowIndex.reindex e w), by
            rw [(mme_dwz_table2_component_projection_certificate
              (K := K) s m).2.2.2]
            exact Submodule.subset_span
              ⟨MME.DWZComponentRestriction.PowIndex.reindex e w,
                (mme_dwz_component_word_allowed_reindex_iff s m e w).2 hw,
                rfl⟩⟩ := by
  sorry
