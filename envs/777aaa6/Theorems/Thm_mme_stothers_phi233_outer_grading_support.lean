-- Prove2me | Theorems.Thm_mme_stothers_phi233_outer_grading_support
-- name    : mme_stothers_phi233_outer_grading_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:36:59.496654+00:00
-- url     : https://prove2.me/theorems/a4e86f23-311f-409d-81c8-a0a4a222e6d5
-- title:
--   The literal $\Phi_{233}$ outer grading has exactly the ten Davie--Stothers support types
-- statement:
--   Let $F_q$ be the coarse $(2,3,3)$ constituent of the fourth Kronecker power of the Coppersmith--Winograd tensor, and grade each mode by the grade of its first square factor. Every nonzero block of this five-grading has one of exactly the ten first-square grade triples
--
--   $$
--   (0,1,3),(0,2,2),(0,3,1),(1,0,3),(1,1,2),
--   (1,2,1),(1,3,0),(2,0,2),(2,1,1),(2,2,0).
--   $$
--
--   Thus the abstract ten-symbol alphabet used in the $\Phi_{233}$ type-2 hashing analysis is supported by the literal fourth-power tensor, with no additional outer blocks. This is the support bridge needed to apply cyclic induced-matching pruning to the actual $\Phi_{233}$ constituent.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), especially the ten constituent types displayed in the definition of phi_233 on pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_stothers_phi233_outer_grading
import Definitions.Def_mme_stothers_phi233_profile_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_outer_grading_support
    {K : Type u} [Field K] (q : Nat) (sigma : Fin 3 -> Fin 5)
    (h : (MME.StothersFourth.Phi233.outerGrading K q).blockTensor sigma ≠ 0) :
    ∃ r : Fin 10, sigma = MME.StothersFourth.Phi233.pattern r := by
  sorry
