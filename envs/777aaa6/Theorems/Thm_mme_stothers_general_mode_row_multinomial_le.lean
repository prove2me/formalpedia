-- Prove2me | Theorems.Thm_mme_stothers_general_mode_row_multinomial_le
-- name    : mme_stothers_general_mode_row_multinomial_le
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:30:52.613865+00:00
-- url     : https://prove2.me/theorems/675baaf2-9bf0-40d6-9430-48610ced180c
-- title:
--   Row multinomials under a conditional-entropy comparison
-- statement:
--   **Row multinomials are dominated by those of a maximum-entropy competitor.**
--
--   Fix an integral ten-class profile $\beta$, a scale $m$, a mode $i$, and a second integral profile
--   $\beta^{*}$ with the *same* nine-grade marginals. Let $k$ be any $45$-cell histogram whose three
--   marginals are the prescribed $M_j = M_j(\beta)m$, and suppose the conditional entropies satisfy
--
--   $$\sum_{j} M_j\,H\!\left(\frac{k|_j}{M_j}\right) \;\le\; \sum_j M_j\,H\!\left(\frac{T^{*}|_j}{M_j}\right),$$
--
--   where $T^{*}$ is the exact histogram of $\beta^{*}$ and $x|_j$ denotes the restriction to the
--   supported triples whose $i$-th coordinate is $j$. Then the row multinomials obey
--
--   $$\prod_{j}\binom{M_j}{k|_j} \;\le\; \bigl(6(N+1)\bigr)^{45}\prod_j \binom{M_j}{T^{*}|_j},$$
--
--   with $N = 3Dm$ the address length.
--
--   This is the passage from an entropy inequality to a counting inequality. Each side is a product of
--   nine multinomial coefficients, and a multinomial coefficient is bounded above by the exponential of
--   the corresponding entropy and below by that exponential divided by a polynomial in the row total;
--   the nine polynomial factors combine into $\bigl(6(N+1)\bigr)^{45}$ because the numbers of supported
--   triples over the nine grades sum to $45$ and each row total is at most $N$.
--
--   Together with the regrouping of the nine row multinomials into a single quotient
--   $\prod_j M_j!/\prod_\sigma k_\sigma!$, this is what turns the entropy comparison of Lemma 5.2 into
--   the star-degree bound driving the outer hash.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4), and Lemma 5.2; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_mode_row_multinomial_le
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (i : Fin 3)
    (k : MME.StothersFourth.GenHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
        sigma.1 l = j}, k sigma.1) =
        MME.StothersFourth.genMarginalCount base m j)
    (hcond :
      (∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = j} ↦
            (k sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = j} ↦
            (MME.StothersFourth.genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ))) :
    (∏ j : Fin 9,
        (Nat.multinomial Finset.univ
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = j} ↦ k sigma.1) : ℝ)) ≤
      (6 * (((MME.StothersFourth.genOuterLength base m + 1 : ℕ) : ℝ))) ^ 45 *
        ∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
                sigma.1 i = j} ↦
              MME.StothersFourth.genHashTargetJointTable bstar m sigma.1) : ℝ) := by
  sorry
