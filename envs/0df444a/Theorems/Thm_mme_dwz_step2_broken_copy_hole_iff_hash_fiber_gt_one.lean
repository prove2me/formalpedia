-- Prove2me | Theorems.Thm_mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one
-- name    : mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:17:37.855663+00:00
-- url     : https://prove2.me/theorems/d0e34473-c92b-4ac5-80d9-680993553a72
-- title:
--   DWZ Step 2: holes are exactly non-singleton compatible retained hash fibers
-- statement:
--   Fix a useful small Z-block z, a retained outer copy J, and one choice w of the affine-hash parameters. Assume z is compatible with J and J is retained by w. Form the Step-2 broken copy using compatibility together with retention in this fixed hash bucket. Then z is a hole of J exactly when the compatible retained fiber above z contains more than one outer copy:
--
--   $$z\text{ is a hole of }J \quad\Longleftrightarrow\quad 1<|\{A:A\sim z\text{ and }A\text{ is retained by }w\}|.$$
--
--   This turns the combinatorial collision event controlled by the asymmetric-hashing estimates into the literal hole event required by the Hole Lemma.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Additional Zeroing-Out Step 2 and Claim 6.8 in Section 6.1, together with Definition 5.5.

import Theorems.Thm_mme_dwz_step2_broken_copy_hole_iff_competitor
import Theorems.Thm_mme_dwz_step2_pointwise_competitor_iff_hash_fiber_gt_one

set_option autoImplicit false

theorem mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one
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
  sorry
