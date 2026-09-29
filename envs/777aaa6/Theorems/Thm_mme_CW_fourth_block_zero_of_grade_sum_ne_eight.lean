-- Prove2me | Theorems.Thm_mme_CW_fourth_block_zero_of_grade_sum_ne_eight
-- name    : mme_CW_fourth_block_zero_of_grade_sum_ne_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:05:01.16038+00:00
-- url     : https://prove2.me/theorems/9fa1eacd-c140-4eeb-bdb2-9e950c56ae7d
-- title:
--   Every unsupported block of the literal fourth CW power vanishes
-- statement:
--   For every field $K$ and every Coppersmith--Winograd parameter $q$, the canonical graded block of the literal fourth power $CW_q^{\otimes 4}$ vanishes whenever the three grade entries do not sum to eight. This is an exact source-level support theorem, obtained from the literal fourfold expansion rather than from an assumed combinatorial support. It applies unchanged to the $q=6$ Stothers source and the $q=5$ DWZ source.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173.

import Definitions.Def_mme_CW_fourth_literal_support_words

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_CW_fourth_block_zero_of_grade_sum_ne_eight
    {K : Type u} [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) ≠ 8) :
    (MME.StothersFourth.cwFourthCanonicalGrading K q).blockTensor sigma = 0 := by
  sorry
