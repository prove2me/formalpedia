-- Prove2me | Theorems.Thm_mme_dwz_available_block_shuffle_of_pretransitive_action
-- name    : mme_dwz_available_block_shuffle_of_pretransitive_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:25:02.346001+00:00
-- url     : https://prove2.me/theorems/c9a5207f-ece5-4896-b5a8-038295eeff46
-- title:
--   DWZ Hole Lemma: transitive actions give uniform block shuffles
-- statement:
--   Let a finite group G act transitively on a finite type B of available small Z-blocks. Then the action permutations form an `AvailableBlockShuffle B G`: for every source and target block, the number of group elements sending the source to the target is exactly |G|/|B| in the division-free form $$|\{g:g\cdot s=t\}|\,|B|=|G|.$$ The returned shuffle permutation is certified pointwise to be the original G-action. This is the finite group-action mechanism behind Claims 5.8--5.10 in the Hole Lemma.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.2, Claims 5.8--5.10; the cardinality argument is the finite orbit--stabilizer theorem.

import Definitions.Def_mme_dwz_hole_cover_data
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Transitive

set_option autoImplicit false

open Finset
open MME.DWZSquare

universe u v

theorem mme_dwz_available_block_shuffle_of_pretransitive_action
    (Block : Type u) (G : Type v)
    [Fintype Block] [DecidableEq Block]
    [Group G] [Fintype G] [DecidableEq G]
    [MulAction G Block] [MulAction.IsPretransitive G Block] :
    ∃ system : AvailableBlockShuffle Block G,
      ∀ g source, system.move g source = g • source := by
  sorry
