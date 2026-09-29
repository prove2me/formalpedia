-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_mode_row_multinomial_le
-- name    : MME.StothersFourth.mme_stothers_fixed_mode_row_multinomial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:05:28.281717+00:00
-- url     : https://prove2.me/theorems/1bc74653-5216-43be-9b06-4ff153f521d3
-- title:
--   Rowwise multinomial comparison for the fixed Stothers profile
-- statement:
--   Let $k$ be any supported joint table with the fixed Stothers marginal, and fix one mode. The product of the nine row multinomial coefficients of $k$ is bounded by the corresponding product for the fixed target table, up to a polynomial factor:
--
--   $$
--   \prod_{j=0}^{8}\binom{M_j}{(k_\sigma)_{\sigma_i=j}}
--   \le \bigl(6(N+1)\bigr)^{45}
--   \prod_{j=0}^{8}\binom{M_j}{(k^*_\sigma)_{\sigma_i=j}}.
--   $$
--
--   Global maximum entropy of the fixed table compares the total conditional entropies, while rowwise upper and lower multinomial bounds introduce only the displayed degree-$45$ polynomial loss.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equation (3.4), printed pp. 354--356, specialized using Section 5, Equation (5.2), printed pp. 367--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; the explicit polynomial factor follows from standard multinomial entropy bounds.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Mathlib.Data.Nat.Choose.Multinomial

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_mode_row_multinomial_le
    (m : ℕ) (hm : 0 < m) (i : Fin 3)
    (k : MME.StothersFourth.FixedHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple // sigma.1 l = j},
        k sigma.1) = MME.StothersFourth.fixedMarginalCount m j) :
    (∏ j : Fin 9,
        (Nat.multinomial Finset.univ
          (fun sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple // sigma.1 i = j} ↦
            k sigma.1) : ℝ)) ≤
      (6 * (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 45 *
        ∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple // sigma.1 i = j} ↦
              MME.StothersFourth.fixedHashTargetJointTable m sigma.1) : ℝ) := by
  sorry
