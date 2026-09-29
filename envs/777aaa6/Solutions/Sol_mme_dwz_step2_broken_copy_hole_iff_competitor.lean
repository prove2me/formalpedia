-- Prove2me | solution 1 for mme_dwz_step2_broken_copy_hole_iff_competitor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:15:44.19747+00:00
-- url     : https://prove2.me/submissions/98f6d980-4337-4b88-865c-6d438b659444

import Definitions.Def_mme_dwz_step2_broken_copy

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Block Copy : Type*}
    [Fintype Block] [DecidableEq Block]
    [Fintype Copy] [DecidableEq Copy]
    (compatible useful : Block → Copy → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (z : Block) (j : Copy)
    (hUseful : useful z j) (hCompatible : compatible z j) :
    z ∉ (MME.DWZStep2.brokenCopy compatible useful j).nonholes ↔
      ∃ j' : Copy, j' ≠ j ∧ compatible z j' := by
  classical
  simp only [MME.DWZStep2.brokenCopy, Finset.mem_filter, Finset.mem_univ,
    true_and, MME.DWZStep2.Keeps, hUseful, hCompatible, true_and]
  constructor
  · intro h
    push_neg at h
    rcases h with ⟨j', hj', hne⟩
    exact ⟨j', hne, hj'⟩
  · rintro ⟨j', hne, hj'⟩ hUnique
    exact hne (hUnique j' hj')
