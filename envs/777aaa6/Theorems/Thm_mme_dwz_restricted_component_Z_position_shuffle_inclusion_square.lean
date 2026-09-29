-- Prove2me | Theorems.Thm_mme_dwz_restricted_component_Z_position_shuffle_inclusion_square
-- name    : mme_dwz_restricted_component_Z_position_shuffle_inclusion_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:18:29.368583+00:00
-- url     : https://prove2.me/theorems/506eb969-0287-4b5b-9485-d94549b449e9
-- title:
--   DWZ projected-Z shuffles commute with ambient inclusion
-- statement:
--   Fix one of the fifteen Table-2 component types $s$, a scale $m$, and a permutation $e$ of the positions belonging to that component. Let $Z_{s,m}^{\mathrm{avail}}$ be the span of the canonical Z-words with the prescribed split histogram, let $\iota_Z$ be its inclusion into the unrestricted component power, and let $P_{e,Z}$ be the ambient position-permutation automorphism. Then there is an automorphism $E_{e,Z}$ of the available Z-space for which the inclusion square commutes exactly:
--
--   $$
--   \iota_Z\circ E_{e,Z}=P_{e,Z}\circ\iota_Z.
--   $$
--
--   Thus the projected available-word shuffle is not merely abstractly isomorphic to the ambient shuffle: it is the literal restriction of the same label permutation. This is the Z-mode compatibility required in Duan--Wu--Zhou Claim 5.9 before tensorizing the component shuffles into the full standard object. The statement includes components of size zero.
--
--   **Formalization Note** The available Z-space is the grade-zero class of `componentPowerProjectionGrading`; its inclusion is `Submodule.subtype`.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claim 5.9, especially the common relabeling of variables within each component, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Theorems.Thm_mme_dwz_restricted_component_Z_position_shuffle
import Theorems.Thm_mme_kronPow_position_permutation_recursive_basis

open MME MME.TensorObj Module

universe u

set_option autoImplicit false

theorem mme_dwz_restricted_component_Z_position_shuffle_inclusion_square
    {K : Type u} [Field K]
    (s : Fin 15) (m : ℕ)
    (e : Equiv.Perm
      (Fin (MME.DWZTable2Counts.component s * m))) :
    ∃ E :
        (MME.DWZComponentRestriction.restrictedComponentPower K s m).V 2 ≃ₗ[K]
          (MME.DWZComponentRestriction.restrictedComponentPower K s m).V 2,
      (Submodule.subtype
          ((MME.DWZComponentRestriction.componentPowerProjectionGrading
            K s m).classOf 2 0)).comp E.toLinearMap =
        (kronPowModePositionEquiv
          (MME.DWZComponentRestriction.canonicalComponentBlock K s) 2
          (MME.DWZComponentRestriction.canonicalComponentZBasis K s)
          (MME.DWZTable2Counts.component s * m) e).toLinearMap.comp
          (Submodule.subtype
            ((MME.DWZComponentRestriction.componentPowerProjectionGrading
              K s m).classOf 2 0)) := by
  sorry
