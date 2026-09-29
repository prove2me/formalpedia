-- Prove2me | Theorems.Thm_mme_stothers_general_exact_address_block_value
-- name    : mme_stothers_general_exact_address_block_value
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-10T05:42:56.085186+00:00
-- url     : https://prove2.me/theorems/8262020b-5f5a-4e93-83a7-103298601309
-- title:
--   Block value of a general-profile exact address, from Table 1 and Lemma 5.1
-- statement:
--   **The unconditional block value of a general-profile exact outer address.**
--
--   Fix a ten-class profile $\beta$ and an exponent $\tau$ with $2 \le 3\tau \le 3$.  For every scale $m$ and every exact outer address $a$ of profile $\beta$ at that scale, the graded block $B_a$ that $a$ cuts out of $CW_6^{\otimes 4}$ has tau-value at least $W$ for every
--
--   $$0 \le W \;<\; \prod_{r=1}^{10} v_r(\tau)^{\,c_r\, \beta_r m},$$
--
--   where $v_r(\tau)$ are the ten class values of Table 1 and $c_r$ the class multiplicities.
--
--   This is the general-profile counterpart of the published fixed-profile statement: the same claim with the ten-vector of Section 5 replaced by an arbitrary profile.  It takes no hypothesis beyond the range of $\tau$, because the ten class values are themselves unconditional — five of them are the elementary Table 1 rows and five are the recursive values of Lemma 5.1.
--
--   The uniformity in $a$ is what the extraction consumes: the family surviving the hashing step is an uncontrolled subset of the exact addresses, so every member must carry the same block value.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Table 1 and Lemma 5.1; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_general_exact_address_block_value
    {K : Type u} [Field K]
    (base : Fin 10 → ℕ)
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ (m : ℕ) (a : MME.StothersFourth.GenExactOuterAddress base m) (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.genProfileCount base m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock
          (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
        tau W := by
  sorry
