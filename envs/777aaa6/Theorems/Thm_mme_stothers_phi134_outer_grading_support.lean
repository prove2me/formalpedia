-- Prove2me | Theorems.Thm_mme_stothers_phi134_outer_grading_support
-- name    : mme_stothers_phi134_outer_grading_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:30:41.018737+00:00
-- url     : https://prove2.me/theorems/cd7f4b06-fb0e-4f23-9222-26fd03749381
-- title:
--   The literal Phi_134 outer grading has exactly eight support types
-- statement:
--   Let $F_q$ be the coarse $(1,3,4)$ constituent of the fourth Kronecker power of the Coppersmith--Winograd tensor, and grade each mode by the grade of its first square factor. Every nonzero block of this five-grading has one of exactly the eight first-square grade triples
--
--   $$
--   (0,0,4),(0,1,3),(0,2,2),(0,3,1),
--   (1,0,3),(1,1,2),(1,2,1),(1,3,0).
--   $$
--
--   Thus the abstract eight-symbol alphabet used in the $\Phi_{1,3,4}$ hashing analysis is the full support of the literal coarse constituent, with no unaccounted outer blocks. This is the support bridge required for induced address-block zeroing.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iii), p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_outer_grading
import Definitions.Def_mme_stothers_phi134_profile_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_outer_grading_support
    {K : Type u} [Field K] (q : Nat) (sigma : Fin 3 -> Fin 5)
    (h : (MME.StothersFourth.Phi134.outerGrading K q).blockTensor sigma ≠ 0) :
    ∃ r : Fin 8, sigma = MME.StothersFourth.Phi134.pattern r := by
  sorry
