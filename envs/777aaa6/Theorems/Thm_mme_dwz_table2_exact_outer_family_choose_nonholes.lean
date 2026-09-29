-- Prove2me | Theorems.Thm_mme_dwz_table2_exact_outer_family_choose_nonholes
-- name    : mme_dwz_table2_exact_outer_family_choose_nonholes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:49:14.148296+00:00
-- url     : https://prove2.me/theorems/c5383a08-5a7f-4fd2-bbaa-6dc1e277c09c
-- title:
--   Choose one literal Claim-6.8 nonhole in every exact-profile retained copy
-- statement:
--   Let a family of retained outer words all have the exact Table-2 component profile at multiplier $m$. Give each retained copy its own broken-copy finset of surviving useful fine-$Z$ blocks, and suppose every copy satisfies Claim 6.8's division-free seven-eighths certificate. Then one can choose, simultaneously for every retained copy $j$, a literal useful block $z_j$ that belongs to that copy's nonhole finset.
--
--   The chosen family remains dependently typed over the actual outer word of each copy, so no common surrogate block universe or cardinality-only proxy is introduced.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 6.3 and Claim 6.8; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_exact_outer_seven_eighths_has_nonhole

universe u v

set_option autoImplicit false

theorem mme_dwz_table2_exact_outer_family_choose_nonholes
    (m : ℕ) {Copy : Type v} {Position : Type u}
    [Fintype Position] [DecidableEq Position]
    (outer : Copy → Position → Fin 15)
    (hProfile : ∀ j (s : Fin 15),
      Fintype.card {t : Position // outer j t = s} =
        MME.DWZTable2Counts.component s * m)
    (copy : ∀ j : Copy, MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hseven : ∀ j : Copy,
      7 * Fintype.card
          (MME.DWZTable2StandardForm.UsefulBlock m (outer j)) ≤
        8 * (copy j).nonholes.card) :
    ∃ small : ∀ j : Copy,
        MME.DWZTable2StandardForm.UsefulBlock m (outer j),
      ∀ j, small j ∈ (copy j).nonholes := by
  sorry
