-- Prove2me | Theorems.Thm_mme_dwz_step2_broken_copy_nonholes_card_mono_of_injective_map
-- name    : mme_dwz_step2_broken_copy_nonholes_card_mono_of_injective_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:31:13.206957+00:00
-- url     : https://prove2.me/theorems/1578285e-8bad-49fc-b046-07cc25948e5f
-- title:
--   Restricting an injectively embedded competitor family cannot reduce nonholes
-- statement:
--   Let $S$ be a finite selected competitor family, $A$ a finite ambient competitor family, and $f:S\hookrightarrow A$ an injection. Assume that a selected competitor is compatible with a block exactly when its image under $f$ is ambient-compatible. Assume also that ambient usefulness of a block for the distinguished image $f(j)$ implies selected usefulness for $j$. Then
--
--   $$
--   |\operatorname{Nonholes}_A(f(j))|\le |\operatorname{Nonholes}_S(j)|.
--   $$
--
--   Thus deleting competitors along an injective compatibility-preserving embedding can only turn holes into nonholes, never the reverse. This is the finite monotonicity needed when the full fixed-$Z$ family in Claim 6.8 is restricted to the retained owner family used by Additional Zeroing-Out Step 2.
--
--   **Formalization Note** A nonhole is represented by `MME.DWZStep2.brokenCopy`: it is useful, compatible with the distinguished owner, and has no distinct compatible competitor.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.5, Additional Zeroing-Out Step 2 in Section 6.1, and Claim 6.8, printed pp. 47 and 51--57 (PDF pp. 48 and 52--58), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step2_broken_copy
import Mathlib.Data.Finset.Card

set_option autoImplicit false

theorem mme_dwz_step2_broken_copy_nonholes_card_mono_of_injective_map
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
  sorry
