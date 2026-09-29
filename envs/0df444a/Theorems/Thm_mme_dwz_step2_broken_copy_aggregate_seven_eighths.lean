-- Prove2me | Theorems.Thm_mme_dwz_step2_broken_copy_aggregate_seven_eighths
-- name    : mme_dwz_step2_broken_copy_aggregate_seven_eighths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:30:09.280034+00:00
-- url     : https://prove2.me/theorems/89740409-5c73-46e6-98d9-c24e69f74752
-- title:
--   Claim 6.8 gives seven-eighths aggregate mass for literal broken copies
-- statement:
--   Let $B$ be a finite family of useful blocks, $W$ a common finite weight space, and let each weight define a literal Step-2 broken copy of one retained owner. Assume that the retained owner is useful, compatible, and hash-retained for every weight. If, for each block, at most one eighth of the weights produce a compatible hash fiber with more than one owner, then the total number of nonholes across all weights satisfies
--
--   $$
--   7|W||B| ≤ 8\sum_{w\in W}|\operatorname{nonholes}(\operatorname{brokenCopy}_w)|.
--   $$
--
--   This is the division-free aggregate form of DWZ Claim 6.8. It retains one shared weight variable inside the sum and therefore supports a subsequent global averaging argument without asserting a pointwise seven-eighths bound for every owner at one common weight.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8 and Additional Zeroing-Out Step 2; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one
import Theorems.Thm_mme_finset_pointwise_one_eighth_aggregate_nonholes

open BigOperators

set_option autoImplicit false

theorem mme_dwz_step2_broken_copy_aggregate_seven_eighths
    {Block Outer Weight : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Outer] [DecidableEq Outer]
    [Fintype Weight] [DecidableEq Weight]
    (compatible useful : Block → Outer → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (hashRetained : Outer → Weight → Prop)
    [DecidableRel hashRetained]
    (retained : Outer)
    (hUseful : ∀ z : Block, useful z retained)
    (hCompatible : ∀ z : Block, compatible z retained)
    (hHash : ∀ w : Weight, hashRetained retained w)
    (hpointwise : ∀ z : Block,
      8 * (Finset.univ.filter (fun w : Weight ↦
        1 < (Finset.univ.filter (fun A : Outer ↦
          compatible z A ∧ hashRetained A w)).card)).card ≤
        Fintype.card Weight) :
    7 * Fintype.card Weight * Fintype.card Block ≤
      8 * ∑ w : Weight,
        (MME.DWZStep2.brokenCopy
          (fun z A ↦ compatible z A ∧ hashRetained A w)
          useful retained).nonholes.card := by
  sorry
