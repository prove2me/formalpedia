-- Prove2me | Theorems.Thm_mme_dwz_canonicalComponent_selected_fullMap_zero_of_fine_block
-- name    : mme_dwz_canonicalComponent_selected_fullMap_zero_of_fine_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T09:56:47.700151+00:00
-- url     : https://prove2.me/theorems/71280317-5735-4d66-a353-fdaf5ba69be2
-- title:
--   A zero fine block annihilates the full-square extension of a selected component map
-- statement:
--   If the fine block selected by three lifted canonical component labels is zero, then the tensor of the full square is annihilated by the three corresponding component singleton maps extended through their canonical coarse-block projectors, even after arbitrary linear postprocessing.
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

theorem mme_dwz_canonicalComponent_selected_fullMap_zero_of_fine_block
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
        (fun i ↦ ((post i).comp
          (MME.DWZComponentRestriction.basisLabelProjection
            (canonicalComponentModeBasis K s i) id {selected i})).comp
          ((cwSquareCanonicalGrading K 6).blockProj i
            (cwSquareBlockType
              (MME.DWZSquare.shapeX s)
              (MME.DWZSquare.shapeY s)
              (MME.DWZSquare.shapeZ s) i)))
        (TensorObj.kron (CWObj K 6) (CWObj K 6)).t = 0 := by
  sorry
