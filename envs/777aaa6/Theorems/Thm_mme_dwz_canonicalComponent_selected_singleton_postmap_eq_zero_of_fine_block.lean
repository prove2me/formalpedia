-- Prove2me | Theorems.Thm_mme_dwz_canonicalComponent_selected_singleton_postmap_eq_zero_of_fine_block
-- name    : mme_dwz_canonicalComponent_selected_singleton_postmap_eq_zero_of_fine_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T00:23:20.2154+00:00
-- url     : https://prove2.me/theorems/eb0e4260-650e-4bc5-a90a-e5ba1d2d1f0a
-- title:
--   A zero fine block annihilates the selected singleton in a Table-2 component
-- statement:
--   Fix one literal Table-2 component of the square of the Coppersmith--Winograd tensor at parameter $q=6$. Choose one canonical component-basis label in each of its three modes. If the fine split block determined by the left and right grades of these three labels is zero, then projecting the component tensor onto these three singleton labels gives the zero tensor, even after arbitrary mode-wise linear postprocessing.
--
--   This is the coordinate-local support lemma needed to justify the paper's first X/Y fine-profile filters before the common-state collision analysis.
-- source:
--   Duan--Wu--Zhou, square Coppersmith--Winograd analysis, Additional Zeroing-Out Step 1; canonical fine-support specialization.

import Definitions.Def_mme_dwz_step1_source_address_projectors
import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_canonicalComponent_selected_singleton_postmap_eq_zero_of_fine_block
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
    (hzero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ fineSplitGrade
        (selected i).leftGrade (selected i).rightGrade) = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (MME.DWZComponentRestriction.basisLabelProjection
            (canonicalComponentModeBasis K s i) id {selected i}))
        (MME.DWZComponentRestriction.canonicalComponentBlock K s).t = 0 := by
  sorry
