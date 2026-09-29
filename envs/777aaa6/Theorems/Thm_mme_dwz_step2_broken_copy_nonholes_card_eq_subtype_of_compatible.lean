-- Prove2me | Theorems.Thm_mme_dwz_step2_broken_copy_nonholes_card_eq_subtype_of_compatible
-- name    : mme_dwz_step2_broken_copy_nonholes_card_eq_subtype_of_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:38:21.928659+00:00
-- url     : https://prove2.me/theorems/183caf4e-fd82-4ab2-8653-677d33e68bb8
-- title:
--   Exact nonhole preservation after restricting to all compatible competitors
-- statement:
--   Let $B$ be a finite block set, let $C$ be a finite competitor set, and let $P\subseteq C$. Fix $j\in P$. Suppose every competitor compatible with any block already belongs to $P$. Restrict both compatibility and usefulness from $C$ to the subtype $P$. Then the ambient and restricted broken copies have exactly the same number of nonholes:
--
--   $$
--   |\operatorname{Nonholes}_{C}(j)|=|\operatorname{Nonholes}_{P}(j)|.
--   $$
--
--   No potential hole-producing competitor is removed by this restriction, so uniqueness of the compatible owner is unchanged. In the asymmetric-hashing construction, this transports the full fixed-$Z$ nonhole count to the subtype of retained owners sharing the selected coarse $Z$-address.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.5 and Additional Zeroing-Out Step 2 in Section 6.1, printed pp. 47 and 51--57 (PDF pp. 48 and 52--58), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step2_broken_copy

set_option autoImplicit false

theorem mme_dwz_step2_broken_copy_nonholes_card_eq_subtype_of_compatible
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
  sorry
