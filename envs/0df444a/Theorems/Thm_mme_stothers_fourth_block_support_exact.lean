-- Prove2me | Theorems.Thm_mme_stothers_fourth_block_support_exact
-- name    : mme_stothers_fourth_block_support_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T18:55:15.743222+00:00
-- url     : https://prove2.me/theorems/de6d4250-1f43-4408-8b50-9d10219b7cad
-- title:
--   Exact support of the canonical fourth power
-- statement:
--   Let $K$ be an arbitrary field and equip the literal tensor $CW_6^{\otimes 4}$ with its canonical nine-grading. For every ordered grade triple $\sigma=(i,j,k)$,
--
--   $$
--   \operatorname{blockTensor}(\sigma)=0\quad\Longleftrightarrow\quad i+j+k\ne 8.
--   $$
--
--   Thus the grading has no unsupported nonzero block, while every grade triple summing to eight is represented by a nonzero literal source block. This is the exact-support statement needed to turn the formal grading into the 45-constituent decomposition of Section 5.
-- source:
--   Davie and Stothers (2013), Section 5, paragraph preceding Lemma 5.1, printed p. 363, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_fourth_block_support_exact
    {K : Type u} [Field K] :
    ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma = 0 ↔
        (∑ s, (sigma s).val) ≠ 8 := by
  sorry
