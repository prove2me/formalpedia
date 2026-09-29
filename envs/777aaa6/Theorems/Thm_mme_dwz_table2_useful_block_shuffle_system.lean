-- Prove2me | Theorems.Thm_mme_dwz_table2_useful_block_shuffle_system
-- name    : mme_dwz_table2_useful_block_shuffle_system
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:55:40.094995+00:00
-- url     : https://prove2.me/theorems/55d886af-c5ee-4496-9fbc-10a767f3771a
-- title:
--   DWZ Claims 5.8--5.10: the concrete Table-2 uniform shuffle system
-- statement:
--   For every fixed Table-2 outer word, the paper's within-component position-permutation group supplies a concrete uniform shuffle system on its available small Z-blocks. Its move is exactly inverse reindexing by the chosen position permutation. For every source and target available block, the exact finite fiber identity is $$|\{\phi:\phi\cdot z=z'\}|\,|\mathcal B_I|=|G_I|,$$ where $\mathcal B_I$ is the useful-block set and $G_I$ is the product of component-fiber symmetric groups. This packages Claims 5.8--5.10 in the interface consumed by the formal Hole-Lemma cover theorem.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.3--5.7 and Claims 5.8--5.10, PDF pp. 48--50 / printed pp. 47--49.

import Theorems.Thm_mme_dwz_available_block_shuffle_of_pretransitive_action
import Theorems.Thm_mme_dwz_table2_useful_block_shuffle_pretransitive

set_option autoImplicit false

open MME.DWZSquare
open MME.DWZTable2StandardForm

universe u

theorem mme_dwz_table2_useful_block_shuffle_system
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15) :
    ∃ system : AvailableBlockShuffle
        (UsefulBlock m outer) (UsefulBlockShuffleGroup outer),
      ∀ g small, system.move g small = g • small := by
  sorry
