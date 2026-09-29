-- Prove2me | Theorems.Thm_mme_dwz_arbitrary_coarse_component_singleton_zero_of_fine_block
-- name    : mme_dwz_arbitrary_coarse_component_singleton_zero_of_fine_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:34:10.013111+00:00
-- url     : https://prove2.me/theorems/3b28d418-f8f7-4a14-9827-02751560c6d4
-- title:
--   Fine-block zero annihilates a singleton in any square-CW coarse component
-- statement:
--   In an arbitrary coarse component of the squared Coppersmith--Winograd tensor, a selected lifted coarse-pair singleton is annihilated after arbitrary postmaps whenever the corresponding fine block tensor vanishes.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_arbitrary_coarse_component_singleton_zero_of_fine_block
    {K : Type u} [Field K] (coarse : Fin 3 → Fin 5)
    (selected : ∀ i,
      DWZComponentRestriction.LiftedCoarsePair.{u} 6 (coarse i))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      ((cwSquareCanonicalGrading K 6).blockSubtensor coarse).V i →ₗ[K]
        W i)
    (hzero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ fineSplitGrade
        (selected i).leftGrade (selected i).rightGrade) = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (DWZComponentRestriction.basisLabelProjection
            (arbitraryCoarseComponentModeBasis K coarse i) id {selected i}))
        ((cwSquareCanonicalGrading K 6).blockSubtensor coarse).t = 0 := by
  sorry
