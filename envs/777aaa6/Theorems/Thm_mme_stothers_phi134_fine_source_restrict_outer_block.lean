-- Prove2me | Theorems.Thm_mme_stothers_phi134_fine_source_restrict_outer_block
-- name    : mme_stothers_phi134_fine_source_restrict_outer_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:40:59.753312+00:00
-- url     : https://prove2.me/theorems/cea0e4b1-e2e7-41b9-a99a-1f6ad6e8c11f
-- title:
--   The eight phi_134 fine sources occupy their prescribed outer blocks
-- statement:
--   For each of the eight ordered fine types $$004,013,022,031,103,112,121,130,$$ let $F_r$ be its literal ordered square-block tensor inside the fourth Coppersmith--Winograd power. Then $F_r$ is a restriction of the block of the internal five-grading of $\Phi_{1,3,4}$ whose three-mode address is that fine type. This finite atlas identifies every source tensor in the exact-profile product with the literal block address used by the hashing argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iii), printed p. 365, the eight fine constituents of T_{134}; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi134_profile_data
import Definitions.Def_mme_stothers_phi134_outer_grading
import Theorems.Thm_mme_stothers_phi134_fine_block_restrict_outer_block

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_fine_source_restrict_outer_block
    {K : Type u} [Field K] (q : ℕ) (r : Fin 8) :
    TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q r)
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor
        (MME.StothersFourth.Phi134.pattern r)) := by
  sorry
