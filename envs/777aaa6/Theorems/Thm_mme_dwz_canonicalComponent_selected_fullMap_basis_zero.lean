-- Prove2me | Theorems.Thm_mme_dwz_canonicalComponent_selected_fullMap_basis_zero
-- name    : mme_dwz_canonicalComponent_selected_fullMap_basis_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T09:29:03.802787+00:00
-- url     : https://prove2.me/theorems/c1cc03e3-6523-4e6c-bfc1-e5577e6ac8b3
-- title:
--   A nonselected full-square basis label is killed by a selected component map
-- statement:
--   For a canonical Table-2 component, extend a selected component-basis singleton map back to the full square through the canonical coarse-block projector. Every full-square canonical basis label other than the selected label is sent to zero, even after arbitrary linear postprocessing.
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

theorem mme_dwz_canonicalComponent_selected_fullMap_basis_zero
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
    (i : Fin 3) (p : Fin 8 × Fin 8)
    (hp : p ≠ (selected i).down.1) :
    post i
        (MME.DWZComponentRestriction.basisLabelProjection
          (canonicalComponentModeBasis K s i) id {selected i}
          ((cwSquareCanonicalGrading K 6).blockProj i
            (cwSquareBlockType
              (MME.DWZSquare.shapeX s)
              (MME.DWZSquare.shapeY s)
              (MME.DWZSquare.shapeZ s) i)
            (cwSquareCanonicalBasis K 6 i p))) = 0 := by
  sorry
