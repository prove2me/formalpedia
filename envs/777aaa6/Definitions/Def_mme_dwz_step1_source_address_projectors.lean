-- Prove2me | Definitions.Def_mme_dwz_step1_source_address_projectors
-- name    : mme_dwz_step1_source_address_projectors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T22:19:09.87939+00:00
-- url     : https://prove2.me/theorems/3e293067-6c56-45b1-9339-b28eae0802f6
-- title:
--   DWZ Step-1 source-address X/Y projectors
-- statement:
--   Inside one literal Table-2 coarse address block, define two diagonal canonical-word projectors. The X projector keeps exactly the X words satisfying every boundary split-profile constraint from Additional Zeroing-Out Step 1, and the Y projector keeps exactly the analogous Y words. These are the X/Y zeroing maps applied before the Step-2 Z-only nonhole projection.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 1, printed p. 51 (PDF p. 52), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_source_address_filters
import Definitions.Def_mme_dwz_basis_label_projection

open MME Module

universe u

namespace MME.DWZSourceAligned

set_option autoImplicit false

/-- Project the X mode of a coarse address block onto the canonical words whose boundary split histograms pass Additional Zeroing-Out Step 1. -/
noncomputable def addressXStep1Projector
    (K : Type u) [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15) :
    (coarseAddressObj K outer).V 0 →ₗ[K]
      (coarseAddressObj K outer).V 0 := by
  classical
  exact MME.DWZComponentRestriction.basisLabelProjection
    (coarseAddressModeBasis K outer 0) id
    (Finset.univ.filter (addressXWordPassesStep1 m outer))

/-- Project the Y mode of a coarse address block onto the canonical words whose boundary split histograms pass Additional Zeroing-Out Step 1. -/
noncomputable def addressYStep1Projector
    (K : Type u) [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15) :
    (coarseAddressObj K outer).V 1 →ₗ[K]
      (coarseAddressObj K outer).V 1 := by
  classical
  exact MME.DWZComponentRestriction.basisLabelProjection
    (coarseAddressModeBasis K outer 1) id
    (Finset.univ.filter (addressYWordPassesStep1 m outer))

end MME.DWZSourceAligned


