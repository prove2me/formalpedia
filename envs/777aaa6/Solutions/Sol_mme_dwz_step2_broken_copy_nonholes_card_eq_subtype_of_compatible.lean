-- Prove2me | solution 1 for mme_dwz_step2_broken_copy_nonholes_card_eq_subtype_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:38:33.891878+00:00
-- url     : https://prove2.me/submissions/ca3b16f7-ea5a-4891-8d55-dde77a2672a8

import Definitions.Def_mme_dwz_step2_broken_copy

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Block Copy : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Copy] [DecidableEq Copy]
    (P : Copy → Prop) [DecidablePred P]
    (compatible useful : Block → Copy → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (j : Copy) (hj : P j)
    (hout : ∀ z j', compatible z j' → P j') :
    (MME.DWZStep2.brokenCopy compatible useful j).nonholes.card =
      (MME.DWZStep2.brokenCopy
        (fun z (jP : Subtype P) ↦ compatible z jP.1)
        (fun z (jP : Subtype P) ↦ useful z jP.1)
        ⟨j, hj⟩).nonholes.card := by
  congr 1
  ext z
  simp only [MME.DWZStep2.brokenCopy, Finset.mem_filter,
    Finset.mem_univ, true_and, MME.DWZStep2.Keeps]
  constructor
  · rintro ⟨hUseful, hCompatible, hUnique⟩
    refine ⟨hUseful, hCompatible, ?_⟩
    intro jP hjP
    apply Subtype.ext
    exact hUnique jP.1 hjP
  · rintro ⟨hUseful, hCompatible, hUnique⟩
    refine ⟨hUseful, hCompatible, ?_⟩
    intro j' hj'
    have hjP : P j' := hout z j' hj'
    exact congrArg Subtype.val (hUnique ⟨j', hjP⟩ hj')
