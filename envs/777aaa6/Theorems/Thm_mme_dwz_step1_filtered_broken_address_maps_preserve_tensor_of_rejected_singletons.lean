-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_broken_address_maps_preserve_tensor_of_rejected_singletons
-- name    : mme_dwz_step1_filtered_broken_address_maps_preserve_tensor_of_rejected_singletons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T23:10:31.011667+00:00
-- url     : https://prove2.me/theorems/042f8679-eb5c-42c5-94c9-828cb2b25f1b
-- title:
--   Two rejected-singleton tests imply Step-1 diagonal absorption
-- statement:
--   Fix one literal coarse Table-2 source address and one selected Step-2 broken copy. Assume every rejected canonical X-word singleton slice vanishes, and, after the X filter has been inserted, every rejected canonical Y-word singleton slice also vanishes. Then applying both Step-1 word filters followed by the broken-copy block projectors maps the coarse-address tensor exactly to the tensor of the whole broken copy. This separates the semantic Step-1 support argument from the finite-basis linear algebra.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Steps 1 and 2, printed pp. 51--52 (PDF pp. 52--53), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_broken_owner_maps
import Theorems.Thm_mme_piTensorProduct_map_basis_filter_eq_of_rejected_singletons_zero

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open MME.DWZSourceAligned

/-- Once the rejected X slices and the rejected Y slices after X filtering
are known to vanish, the two Step-1 basis filters preserve the tensor of one
whole broken owner.  This is the exact algebraic capstone separating the two
semantic singleton-zero leaves from the final diagonal tensor identity. -/

theorem mme_dwz_step1_filtered_broken_address_maps_preserve_tensor_of_rejected_singletons
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (hXZero : ∀ (x : AddressModeWord outer 0),
      ¬ addressXWordPassesStep1 m outer x →
      let G := brokenAddressGrading K m outer copy
      let base : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
        fun i ↦ G.blockProj i 0
      let singleton :=
        DWZComponentRestriction.basisLabelProjection
          (coarseAddressModeBasis K outer 0) id {x}
      PiTensorProduct.map
        (Function.update base 0 ((base 0).comp singleton))
        (coarseAddressObj K outer).t = 0)
    (hYZero : ∀ (y : AddressModeWord outer 1),
      ¬ addressYWordPassesStep1 m outer y →
      let G := brokenAddressGrading K m outer copy
      let base : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
        fun i ↦ G.blockProj i 0
      let xMaps := Function.update base 0
        ((base 0).comp (addressXStep1Projector K m outer))
      let singleton :=
        DWZComponentRestriction.basisLabelProjection
          (coarseAddressModeBasis K outer 1) id {y}
      PiTensorProduct.map
        (Function.update xMaps 1 ((xMaps 1).comp singleton))
        (coarseAddressObj K outer).t = 0) :
    PiTensorProduct.map
        (step1FilteredBrokenAddressMaps K m outer copy)
        (coarseAddressObj K outer).t =
      (brokenAddressObj K m outer copy).t := by sorry
