-- Prove2me | solution 1 for mme_dwz_canonicalComponent_selected_singleton_postmap_eq_zero_of_fine_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:12:32.58998+00:00
-- url     : https://prove2.me/submissions/29a16c57-8891-498c-8f67-c591eb7d3a5f

import Definitions.Def_mme_dwz_step1_source_address_projectors
import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Theorems.Thm_mme_dwz_canonicalComponent_selected_fullMap_zero_of_fine_block

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem solution
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
  let componentMaps := fun i ↦ (post i).comp
    (MME.DWZComponentRestriction.basisLabelProjection
      (canonicalComponentModeBasis K s i) id {selected i})
  let blockMaps := fun i ↦ (cwSquareCanonicalGrading K 6).blockProj i
    (cwSquareBlockType
      (MME.DWZSquare.shapeX s)
      (MME.DWZSquare.shapeY s)
      (MME.DWZSquare.shapeZ s) i)
  have hfull :=
    mme_dwz_canonicalComponent_selected_fullMap_zero_of_fine_block
      (K := K) s selected post hzero
  change PiTensorProduct.map componentMaps
      (PiTensorProduct.map blockMaps
        (TensorObj.kron (CWObj K 6) (CWObj K 6)).t) = 0
  calc
    _ = PiTensorProduct.map
        (fun i ↦ (componentMaps i).comp (blockMaps i))
        (TensorObj.kron (CWObj K 6) (CWObj K 6)).t := by
          simpa only [LinearMap.comp_apply] using
            (LinearMap.congr_fun
              (PiTensorProduct.map_comp
                (f := blockMaps) (g := componentMaps))
              (TensorObj.kron (CWObj K 6) (CWObj K 6)).t).symm
    _ = PiTensorProduct.map
        (fun i ↦ ((post i).comp
          (MME.DWZComponentRestriction.basisLabelProjection
            (canonicalComponentModeBasis K s i) id {selected i})).comp
          ((cwSquareCanonicalGrading K 6).blockProj i
            (cwSquareBlockType
              (MME.DWZSquare.shapeX s)
              (MME.DWZSquare.shapeY s)
              (MME.DWZSquare.shapeZ s) i)))
        (TensorObj.kron (CWObj K 6) (CWObj K 6)).t := by
          rfl
    _ = 0 := hfull
