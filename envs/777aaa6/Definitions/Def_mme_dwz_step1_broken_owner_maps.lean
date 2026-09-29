-- Prove2me | Definitions.Def_mme_dwz_step1_broken_owner_maps
-- name    : mme_dwz_step1_broken_owner_maps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T22:37:36.458801+00:00
-- url     : https://prove2.me/theorems/19c1af43-82ad-4005-b296-13a2991e6906
-- title:
--   Step-1-filtered maps for a broken Table-2 source owner
-- statement:
--   For one literal Table-2 coarse address, define the modewise linear maps used in the paper-faithful source degeneration. The X and Y modes first pass through the boundary-histogram projectors from Additional Zeroing-Out Step 1, while the Z mode is unchanged; all three modes then pass through the block projector selecting the chosen Step-2 broken copy. A second family of maps prepends the canonical coarse-address projector from the full squared Coppersmith--Winograd power.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Steps 1 and 2, printed pp. 51--52 (PDF pp. 52--53), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_source_address_projectors

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZSourceAligned

/-- The modewise Step-1 projector on one coarse address: the paper's X and Y
word filters in modes zero and one, and the identity in mode two. -/
noncomputable def addressStep1Projector
    (K : Type u) [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15) :
    ∀ i : Fin 3,
      (coarseAddressObj K outer).V i →ₗ[K]
        (coarseAddressObj K outer).V i :=
  fun i ↦ Fin.cases
    (addressXStep1Projector K m outer)
    (Fin.cases
      (addressYStep1Projector K m outer)
      (fun _ ↦ LinearMap.id)) i

/-- Maps from one coarse address to its Step-2 broken object after inserting
the paper-faithful Step-1 X/Y word filters. -/
noncomputable def step1FilteredBrokenAddressMaps
    (K : Type u) [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    ∀ i : Fin 3,
      (coarseAddressObj K outer).V i →ₗ[K]
        (brokenAddressObj K m outer copy).V i :=
  fun i ↦
    ((brokenAddressGrading K m outer copy).blockProj i 0).comp
      (addressStep1Projector K m outer i)

/-- The literal full-source maps: first select the owner's coarse address,
then apply Step 1 in X/Y, and finally apply the Step-2 surviving-Z mask. -/
noncomputable def step1FilteredBrokenSourceMaps
    (K : Type u) [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    ∀ i : Fin 3,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).V i) →ₗ[K]
        (brokenAddressObj K m outer copy).V i :=
  fun i ↦ (step1FilteredBrokenAddressMaps K m outer copy i).comp
    (gradedAddressProj (cwSquareCanonicalGrading K 6) N
      (coarseAddress outer) i)

end MME.DWZSourceAligned


