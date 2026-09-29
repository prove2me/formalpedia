-- Prove2me | Theorems.Thm_mme_stothers_phi116_four_edge_support
-- name    : mme_stothers_phi116_four_edge_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:34:16.255817+00:00
-- url     : https://prove2.me/theorems/64abf609-c403-4dc8-a6fc-5a41387d7696
-- title:
--   Exact four-edge support of the literal phi_116 outer grading
-- statement:
--   Equip the literal constituent $\varphi_{116}\subset CW_6^{\otimes4}$ with its canonical outer three-grading. Its only possibly nonzero block tensors have addresses
--
--   $$
--   (0,0,0),\qquad (1,1,1),\qquad (0,1,2),\qquad (1,0,2).
--   $$
--
--   Equivalently, every block at an address distinct from all four displayed triples is zero. This is the exact support hypothesis needed by the four-edge Salem--Spencer hashing construction for Lemma 5.1(i), and it concerns the literal graded constituent rather than an external direct-sum surrogate.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_outer_grading

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_four_edge_support
    {K : Type u} [Field K] :
    ∀ sigma : Fin 3 → Fin 3,
      sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
      sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
      (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockTensor sigma = 0 := by
  sorry
