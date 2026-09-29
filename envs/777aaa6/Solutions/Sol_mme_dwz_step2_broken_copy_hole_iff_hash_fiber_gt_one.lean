-- Prove2me | solution 1 for mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:20:09.361987+00:00
-- url     : https://prove2.me/submissions/5389fc6a-3288-4f45-9fb7-1f0c30c62923

import Theorems.Thm_mme_dwz_step2_broken_copy_hole_iff_competitor
import Theorems.Thm_mme_dwz_step2_pointwise_competitor_iff_hash_fiber_gt_one

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Block Outer Weight : Type*}
    [Fintype Block] [DecidableEq Block]
    [Fintype Outer] [DecidableEq Outer]
    (compatible useful : Block → Outer → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (hashRetained : Outer → Weight → Prop)
    [DecidableRel hashRetained]
    (z : Block) (retained : Outer) (w : Weight)
    (hUseful : useful z retained)
    (hCompatible : compatible z retained)
    (hHash : hashRetained retained w) :
    z ∉ (MME.DWZStep2.brokenCopy
      (fun z A => compatible z A ∧ hashRetained A w) useful retained).nonholes ↔
      1 < (Finset.univ.filter
        (fun A : Outer => compatible z A ∧ hashRetained A w)).card := by
  classical
  rw [mme_dwz_step2_broken_copy_hole_iff_competitor
    (fun z A => compatible z A ∧ hashRetained A w) useful z retained
    hUseful ⟨hCompatible, hHash⟩]
  exact (mme_dwz_step2_pointwise_competitor_iff_hash_fiber_gt_one
    (fun A => compatible z A) hashRetained retained w hCompatible hHash).symm
