-- Prove2me | solution 1 for mme_dwz_restricted_component_Z_position_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:39:58.965608+00:00
-- url     : https://prove2.me/submissions/3d64d092-2767-4ddc-8902-5488530b1a48

import Definitions.Def_mme_basis_index_permutation
import Theorems.Thm_mme_basis_index_permutation_maps_invariant_span
import Theorems.Thm_mme_dwz_component_word_allowed_reindex_iff
import Theorems.Thm_mme_dwz_table2_component_projection_certificate

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
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
  let b := MME.DWZComponentRestriction.componentPowerZBasis K s m
  let allowed := MME.DWZComponentRestriction.componentWordAllowed s m
  let idxE := MME.DWZComponentRestriction.PowIndex.reindexEquiv
    (ι := MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ s)) e
  let P := Submodule.span K (b '' {w | allowed w})
  have hinv : ∀ w, allowed (idxE w) ↔ allowed w := by
    intro w
    exact mme_dwz_component_word_allowed_reindex_iff s m e w
  have hmap :
      Submodule.map
          (MME.DWZComponentRestriction.basisIndexPermEquiv b idxE).toLinearMap P =
        P := by
    exact mme_basis_index_permutation_maps_invariant_span
      b idxE allowed hinv
  let EP : P ≃ₗ[K] P :=
    ((MME.DWZComponentRestriction.basisIndexPermEquiv b idxE).submoduleMap P).trans
      (LinearEquiv.ofEq _ _ hmap)
  have hZ :=
    (mme_dwz_table2_component_projection_certificate (K := K) s m).2.2.2
  let castZ :
      (MME.DWZComponentRestriction.restrictedComponentPower K s m).V 2 ≃ₗ[K] P :=
    LinearEquiv.ofEq _ _ hZ
  let E := castZ.trans (EP.trans castZ.symm)
  refine ⟨E, ?_⟩
  intro w hw
  apply Subtype.ext
  change MME.DWZComponentRestriction.basisIndexPermEquiv b idxE (b w) =
    b (MME.DWZComponentRestriction.PowIndex.reindex e w)
  exact MME.DWZComponentRestriction.basisIndexPermEquiv_apply_basis b idxE w
