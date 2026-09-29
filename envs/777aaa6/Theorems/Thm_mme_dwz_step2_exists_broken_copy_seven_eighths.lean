-- Prove2me | Theorems.Thm_mme_dwz_step2_exists_broken_copy_seven_eighths
-- name    : mme_dwz_step2_exists_broken_copy_seven_eighths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:42:04.771321+00:00
-- url     : https://prove2.me/theorems/7b73e3ef-3492-4b18-bb5d-0ca5b327b357
-- title:
--   DWZ Step 2: one broken copy retains at least seven eighths nonholes
-- statement:
--   Let a retained outer copy be useful and compatible with every small block, and suppose it survives every weight in a nonempty finite conditioned parameter space. A small block is a Step-2 hole precisely when more than one compatible outer copy survives the chosen hash. If, for each block, that collision event occurs for at most one eighth of all weights, then there is one shared weight whose literal Step-2 broken copy has at least seven eighths nonholes, in the division-free form $$7|B| ≤ 8|B_{\mathrm{nonhole}}|.$$ This is the finite Claim 6.8-to-Hole-Lemma interface for the actual broken-copy data structure.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.3, Claim 6.8 and the paragraph 'Bounding the value' immediately following it.

import Theorems.Thm_mme_dwz_claim6_8_exists_seven_eighths_nonholes
import Theorems.Thm_mme_dwz_step2_broken_copy_hole_iff_hash_fiber_gt_one

set_option autoImplicit false

theorem mme_dwz_step2_exists_broken_copy_seven_eighths
    {Block Outer Weight : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Outer] [DecidableEq Outer]
    [Fintype Weight] [DecidableEq Weight] [Nonempty Weight]
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
    ∃ w : Weight,
      7 * Fintype.card Block ≤
        8 * (MME.DWZStep2.brokenCopy
          (fun z A ↦ compatible z A ∧ hashRetained A w)
          useful retained).nonholes.card := by
  sorry
