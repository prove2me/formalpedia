-- Prove2me | solution 1 for mme_dwz_step2_broken_copy_nonholes_card_mono_of_injective_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:31:42.433525+00:00
-- url     : https://prove2.me/submissions/79a17eee-e0ff-4296-8dbe-a1a9ef216168

import Definitions.Def_mme_dwz_step2_broken_copy
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Block Small Big : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Small] [DecidableEq Small]
    [Fintype Big] [DecidableEq Big]
    (smallCompatible smallUseful : Block → Small → Prop)
    [DecidableRel smallCompatible] [DecidableRel smallUseful]
    (bigCompatible bigUseful : Block → Big → Prop)
    [DecidableRel bigCompatible] [DecidableRel bigUseful]
    (f : Small → Big) (hf : Function.Injective f) (j : Small)
    (hcompatible : ∀ z i,
      smallCompatible z i ↔ bigCompatible z (f i))
    (huseful : ∀ z,
      bigUseful z (f j) → smallUseful z j) :
    (MME.DWZStep2.brokenCopy bigCompatible bigUseful (f j)).nonholes.card ≤
      (MME.DWZStep2.brokenCopy
        smallCompatible smallUseful j).nonholes.card := by
  apply Finset.card_le_card
  intro z hz
  simp only [MME.DWZStep2.brokenCopy, Finset.mem_filter,
    Finset.mem_univ, true_and, MME.DWZStep2.Keeps] at hz ⊢
  rcases hz with ⟨hzUseful, hzCompatible, hzUnique⟩
  refine ⟨huseful z hzUseful, (hcompatible z j).mpr hzCompatible, ?_⟩
  intro i hi
  apply hf
  exact hzUnique (f i) ((hcompatible z i).mp hi)
