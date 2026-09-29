-- Prove2me | Theorems.Thm_mme_stothers_fixed_exact_address_block_value
-- name    : mme_stothers_fixed_exact_address_block_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:40:04.876871+00:00
-- url     : https://prove2.me/theorems/0121bfbb-44f3-43b3-b00b-8632a18ab912
-- title:
--   Tau-value of every exact fixed Stothers address block
-- statement:
--   Fix $2\le3\tau\le3$. Every exact fixed-profile outer address block in the canonical nine-grading of the literal fourth Coppersmith--Winograd tensor attains every nonnegative tau-value strictly below $$\prod_{r=0}^9 v_r(\tau)^{n_r c_r(m)}.$$ Here $c_r(m)$ is the exact multiplicity of each ordered member of Table 1 class $r$, and $n_r$ is the number of cyclic triples in that class. The proof must regroup the literal ordered block factors into cyclic symmetrizations, use the elementary values for classes $008$ through $044$, and use Davie--Stothers Lemma 5.1 for classes $116$ through $233$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Table 1, Lemma 5.1, and Theorem 5.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. A. J. Stothers, On the Complexity of Matrix Multiplication, PhD thesis, 2010, Chapter 4.3; https://era.ed.ac.uk/handle/1842/4734.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_fixed_exact_address_block_value
    {K : Type u} [Field K]
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau)
    (htauUpper : 3 * tau ≤ 3) :
    ∀ (m : ℕ) (a : MME.StothersFourth.FixedExactOuterAddress m)
        (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.fixedProfileCount m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock
          (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
        tau W := by
  sorry
