-- Prove2me | Theorems.Thm_mme_stothers_general_completion_quotient_le_polynomial_target
-- name    : mme_stothers_general_completion_quotient_le_polynomial_target
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:32:00.666834+00:00
-- url     : https://prove2.me/theorems/359ce356-bd20-4ff9-b21b-b842ad1b30a9
-- title:
--   Completion quotient against a maximum-entropy profile
-- statement:
--   **The completion quotient is at most polynomially larger than that of a maximum-entropy profile.**
--
--   Fix an integral ten-class profile $\beta$, a scale $m$, a mode $i$, and a second profile
--   $\beta^{*}$ with the same nine-grade marginals. For any $45$-cell histogram $k$ with the
--   prescribed marginals $M_j = M_j(\beta)m$, and under the conditional-entropy comparison
--   $\sum_j M_j H(k|_j/M_j)\le\sum_j M_j H(T^{*}|_j/M_j)$,
--
--   $$\frac{\prod_j M_j!}{\prod_\sigma k_\sigma!}\;\le\;\bigl(6(N+1)\bigr)^{45}\,D_*(\beta^{*}),
--   \qquad D_*(\beta^{*})=\frac{\prod_j M_j!}{\prod_\sigma T^{*}_\sigma!},$$
--
--   with $N=3Dm$ the address length.
--
--   The left-hand side is the number of ways to complete one fixed mode word to a full
--   marginal-supported address with joint histogram $k$; the right-hand side is the same quantity for
--   the reference profile $\beta^{*}$, inflated by a factor polynomial in $N$. So *no* competing
--   histogram on the marginal fibre has a completion star more than polynomially larger than the
--   reference one. When $\beta^{*}$ is the maximum-entropy profile on the fibre this is the statement
--   that the star degree is controlled by $D_*(\beta^{*})$ for every histogram at once, which is the
--   form the outer hashing argument consumes; the ratio $D_*(\beta)/D_*(\beta^{*})$ is then exactly
--   the combination loss of Equation (3.4).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4), and Lemma 5.2; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_completion_quotient_le_polynomial_target
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j = MME.StothersFourth.genMarginalBaseCount base j)
    (i : Fin 3)
    (k : MME.StothersFourth.GenHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 l = j},
        k sigma.1) = MME.StothersFourth.genMarginalCount base m j)
    (hcond :
      (∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
            (k sigma.1 : ℝ) / (MME.StothersFourth.genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
            (MME.StothersFourth.genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ))) :
    (((∏ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j).factorial) /
        ∏ sigma : MME.StothersFourth.GenHashSupportTriple, (k sigma).factorial : ℕ) : ℝ) ≤
      (6 * (((MME.StothersFourth.genOuterLength base m + 1 : ℕ) : ℝ))) ^ 45 *
        (MME.StothersFourth.genHashTargetStarDegree bstar m : ℝ) := by
  sorry
