-- Prove2me | Theorems.Thm_mme_dwz_table2_useful_block_shuffle_pretransitive
-- name    : mme_dwz_table2_useful_block_shuffle_pretransitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:49:10.748964+00:00
-- url     : https://prove2.me/theorems/922a7aa7-91f1-4b06-bc9b-6cc810747a9c
-- title:
--   DWZ Claim 5.10: the useful-block shuffle action is transitive
-- statement:
--   Fix a Table-2 outer component word $I$ and the prescribed integral split multiplicity $m$. The product of symmetric groups which permutes position pairs within each component acts transitively on the available small Z-blocks over $I$. Equivalently, for any two available blocks $z,z'$, there is a component-preserving position permutation $\phi$ such that $$z'_{\phi(t)}=z_t\qquad\text{for every position }t.$$ Thus a uniformly random shuffle sends any fixed available block uniformly across the full available-block set after the finite orbit--stabilizer count is applied.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claim 5.10, PDF pp. 49--50 / printed pp. 48--49.

import Definitions.Def_mme_dwz_table2_useful_block_shuffle_action
import Mathlib.GroupTheory.GroupAction.Transitive

set_option autoImplicit false

open MME.DWZTable2StandardForm

universe u

theorem mme_dwz_table2_useful_block_shuffle_pretransitive
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15) :
    MulAction.IsPretransitive
      (UsefulBlockShuffleGroup outer) (UsefulBlock m outer) := by
  sorry
