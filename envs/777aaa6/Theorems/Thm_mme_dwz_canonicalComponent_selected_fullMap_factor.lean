-- Prove2me | Theorems.Thm_mme_dwz_canonicalComponent_selected_fullMap_factor
-- name    : mme_dwz_canonicalComponent_selected_fullMap_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T09:36:12.296998+00:00
-- url     : https://prove2.me/theorems/6970f876-8b17-4910-a6d9-d1b7b6f97873
-- title:
--   A selected canonical component map factors through its full-square singleton
-- statement:
--   The full-square extension of a selected canonical component map is unchanged when precomposed with the corresponding selected singleton projector on the canonical square basis.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6, canonical component and fine-block source decomposition.

import Definitions.Def_mme_dwz_step1_source_address_projectors
import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_canonicalComponent_selected_fullMap_factor
    {K : Type u} [Field K] (s : Fin 15)
    (selected : ∀ i : Fin 3,
      MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (cwSquareBlockType
          (MME.DWZSquare.shapeX s)
          (MME.DWZSquare.shapeY s)
          (MME.DWZSquare.shapeZ s) i))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      (MME.DWZComponentRestriction.canonicalComponentBlock K s).V i →ₗ[K]
        W i)
    (i : Fin 3) :
    let componentMap := (post i).comp
      (MME.DWZComponentRestriction.basisLabelProjection
        (canonicalComponentModeBasis K s i) id {selected i})
    let fullMap := componentMap.comp
      ((cwSquareCanonicalGrading K 6).blockProj i
        (cwSquareBlockType
          (MME.DWZSquare.shapeX s)
          (MME.DWZSquare.shapeY s)
          (MME.DWZSquare.shapeZ s) i))
    fullMap.comp
        (MME.DWZComponentRestriction.basisLabelProjection
          (cwSquareCanonicalBasis K 6 i) id {(selected i).down.1}) =
      fullMap := by
  sorry
