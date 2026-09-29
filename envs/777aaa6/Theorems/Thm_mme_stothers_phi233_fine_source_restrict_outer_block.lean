-- Prove2me | Theorems.Thm_mme_stothers_phi233_fine_source_restrict_outer_block
-- name    : mme_stothers_phi233_fine_source_restrict_outer_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:18:36.947959+00:00
-- url     : https://prove2.me/theorems/8674cc12-7714-4b0c-a96c-12c752b3f586
-- title:
--   The ten phi_233 fine sources occupy their prescribed outer blocks
-- statement:
--   For each of the ten ordered fine types
--
--   $$
--   013,022,031,103,112,121,130,202,211,220,
--   $$
--
--   let $F_r$ be its literal ordered square-block tensor inside the fourth Coppersmith--Winograd power. Then $F_r$ is a restriction of the block of the internal five-grading of $\varphi_{233}$ whose three-mode address is that fine type. This finite atlas identifies every source tensor in the exact-profile product with the block address used by the hashing argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), printed p. 366, the ten fine constituents of T_{233}; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_stothers_phi233_outer_grading
import Theorems.Thm_mme_stothers_phi233_fine_block_restrict_outer_block

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_fine_source_restrict_outer_block
    {K : Type u} [Field K] (q : ℕ) (r : Fin 10) :
    TensorObj.Restrict
      (MME.StothersFourth.Phi233.fineSourceObj K q r)
      ((MME.StothersFourth.Phi233.outerGrading K q).blockSubtensor
        (MME.StothersFourth.Phi233.pattern r)) := by
  sorry
