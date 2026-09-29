-- Prove2me | Theorems.Thm_mme_dwz_step2_broken_copy_hole_iff_competitor
-- name    : mme_dwz_step2_broken_copy_hole_iff_competitor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:14:30.271408+00:00
-- url     : https://prove2.me/theorems/2e8dc31d-eada-41da-bf67-0004d569cba6
-- title:
--   DWZ Step 2: a hole is exactly a block with a competing compatible copy
-- statement:
--   Fix a useful small Z-block z that is compatible with a retained large copy j. In the public broken-copy object produced by DWZ Additional Zeroing-Out Step 2, z is a hole of j if and only if there exists a different retained copy j' compatible with z. This is the exact finite semantics of the paper's second deletion rule: every small block shared by two surviving large copies is zeroed out from all of them.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Additional Zeroing-Out Step 2 in Section 6.1 and Definition 5.5.

import Definitions.Def_mme_dwz_step2_broken_copy

set_option autoImplicit false

theorem mme_dwz_step2_broken_copy_hole_iff_competitor
    {Block Copy : Type*}
    [Fintype Block] [DecidableEq Block]
    [Fintype Copy] [DecidableEq Copy]
    (compatible useful : Block → Copy → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (z : Block) (j : Copy)
    (hUseful : useful z j) (hCompatible : compatible z j) :
    z ∉ (MME.DWZStep2.brokenCopy compatible useful j).nonholes ↔
      ∃ j' : Copy, j' ≠ j ∧ compatible z j' := by
  sorry
