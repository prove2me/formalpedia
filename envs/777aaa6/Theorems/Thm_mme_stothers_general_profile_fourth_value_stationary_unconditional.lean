-- Prove2me | Theorems.Thm_mme_stothers_general_profile_fourth_value_stationary_unconditional
-- name    : mme_stothers_general_profile_fourth_value_stationary_unconditional
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-10T05:55:37.317585+00:00
-- url     : https://prove2.me/theorems/5890f32d-19c4-405e-9430-28d8f5903f59
-- title:
--   Corrected Theorem 5.3 for integral profiles, without a class-value hypothesis
-- statement:
--   **The corrected Theorem 5.3 for integral profiles, in closed form.**
--
--   Let $\beta$ and $\beta^{*}$ be strictly positive integral ten-class profiles with the same nine-grade marginals, suppose the normalised partner $b = \beta^{*}/D$ is stationary, $b \in \mathcal N$, and let $2 \le 3\tau \le 3$.  Writing $a = \beta/D$, for every
--
--   $$0 \le V \;<\; G(\tau,a)\,\frac{E(b)}{E(a)},
--   \qquad E(x) = \prod_r x_r^{\,c_r x_r},$$
--
--   the literal fourth power $CW_6^{\otimes 4}$ has tau-value at least $V$.
--
--   This is the same statement as the conditional version, with the two structural hypotheses discharged: the ten class values, which come from the elementary Table 1 rows together with the recursive values of Lemma 5.1 and need only the stated range of $\tau$, and the support condition, which says the fourth-power grading is concentrated in total degree eight.  What remains are exactly the arithmetic conditions on the profile pair, which is the form an approximation argument can feed.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Theorem 5.3, Section 5 (Equation (5.2), its kernel, and the set N) and Section 3, Equations (3.2)-(3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_general_profile_fourth_value_stationary_unconditional
    {K : Type u} [Field K]
    (base bstar : Fin 10 → ℕ) (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∀ V : ℝ, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau
            (MME.StothersFourth.genProfileB base)
            (MME.StothersFourth.genProfileB base) *
          (MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB bstar) /
            MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB base)) →
      HasTauValueAtLeast (MME.StothersFourth.cwFourthObj K 6) tau V := by
  sorry
