-- Prove2me | solution 1 for mme_dwz_table2_useful_block_shuffle_system
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:57:13.431274+00:00
-- url     : https://prove2.me/submissions/303420c6-158a-40cc-9ea7-644b688b85e3

import Theorems.Thm_mme_dwz_available_block_shuffle_of_pretransitive_action
import Theorems.Thm_mme_dwz_table2_useful_block_shuffle_pretransitive

set_option autoImplicit false
set_option warningAsError true

open MME.DWZSquare
open MME.DWZTable2StandardForm

universe u

theorem solution
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15) :
    ∃ system : AvailableBlockShuffle
        (UsefulBlock m outer) (UsefulBlockShuffleGroup outer),
      ∀ g small, system.move g small = g • small := by
  letI : MulAction.IsPretransitive
      (UsefulBlockShuffleGroup outer) (UsefulBlock m outer) :=
    mme_dwz_table2_useful_block_shuffle_pretransitive m outer
  exact mme_dwz_available_block_shuffle_of_pretransitive_action
    (UsefulBlock m outer) (UsefulBlockShuffleGroup outer)
