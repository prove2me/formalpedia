-- Prove2me | Theorems.Thm_mme_dwz_source_address_useful_z_supported_implies_step1_words
-- name    : mme_dwz_source_address_useful_z_supported_implies_step1_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T21:53:38.756587+00:00
-- url     : https://prove2.me/theorems/c3c3abe3-642b-4780-ad14-9448bf605588
-- title:
--   Useful supported source words pass both DWZ Step-1 filters
-- statement:
--   Fix a literal Table-2 coarse address. If canonical X-, Y-, and Z-mode basis words form a nonzero fine Coppersmith--Winograd square block at every coordinate and the Z word is useful, then the X word and the Y word satisfy their respective boundary split-histogram predicates from Additional Zeroing-Out Step 1. This is the diagonal absorption statement that lets the Step-1 X/Y projections be inserted into the source restriction without deleting intended useful-Z terms.
-- source:
--   Duan--Wu--Zhou, arXiv:2210.10173, Additional Zeroing-Out Step 1 and Claim 6.2, pp. 50--52.

import Definitions.Def_mme_dwz_step1_source_address_filters
import Theorems.Thm_mme_dwz_table2_useful_z_and_fine_support_implies_step1_xy

open MME MME.DWZStep1Support

universe u

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open MME.DWZSourceAligned

/-- At the literal source-address basis interface, every supported diagonal
term carrying a useful Z word also passes both Step-1 X/Y word filters. -/

theorem mme_dwz_source_address_useful_z_supported_implies_step1_words
    {K : Type u} [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15)
    (xWord : AddressModeWord outer 0)
    (yWord : AddressModeWord outer 1)
    (zWord : AddressZWord outer)
    (hUseful : addressWordUseful m outer zWord)
    (hSupported : ∀ t,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ ![
          fineSplitGrade
            (addressModeLeftGrade xWord t)
            (addressModeRightGrade xWord t),
          fineSplitGrade
            (addressModeLeftGrade yWord t)
            (addressModeRightGrade yWord t),
          fineSplitGrade (zWord t).leftGrade (zWord t).rightGrade] i) ≠ 0) :
    addressXWordPassesStep1 m outer xWord ∧
      addressYWordPassesStep1 m outer yWord := by
  sorry
