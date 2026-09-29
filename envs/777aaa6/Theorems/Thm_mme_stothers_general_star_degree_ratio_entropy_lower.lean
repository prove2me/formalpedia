-- Prove2me | Theorems.Thm_mme_stothers_general_star_degree_ratio_entropy_lower
-- name    : mme_stothers_general_star_degree_ratio_entropy_lower
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T05:37:03.923635+00:00
-- url     : https://prove2.me/theorems/3c5cca33-05f9-4608-927d-776888e76549
-- title:
--   The star-degree ratio of two profiles is the entropy-product ratio
-- statement:
--   **The combination loss is the entropy-product ratio, up to a polynomial factor.**
--
--   Let $\beta$ and $\beta^{*}$ be strictly positive integral ten-class profiles with the same nine-grade marginals, $Q\beta^{*} = Q\beta$, and write $a = \beta/D$ and $b = \beta^{*}/D$ for the normalised profiles, $N = 3Dm$ for the address length, and
--
--   $$\Delta_\gamma(m) \;=\; \frac{\prod_{j} \bigl((Q\beta)_j m\bigr)!}{\prod_{\sigma} \mu_\gamma(m,\sigma)!}$$
--
--   for the star degree of a profile $\gamma$ on that marginal fibre.  Then for every $m \ge 1$
--
--   $$\left(\frac{E(b)}{E(a)}\right)^{N} \;\le\; \bigl(6(N+1)\bigr)^{45}\,\frac{\Delta_\beta(m)}{\Delta_{\beta^{*}}(m)},
--   \qquad E(x) = \prod_{r} x_r^{\,c_r x_r}.$$
--
--   This is the last analytic link in the general-profile chain.  The outer capacity of $\beta$ against a stationary partner $\beta^{*}$ carries the star-degree ratio as its combination loss; this statement says that ratio is, at exponential rate, exactly the entropy-product ratio $E(b)/E(a)$ appearing in the corrected Theorem 5.3.  On the diagonal $\beta = \beta^{*}$ both sides are $1$ up to the polynomial, which is why the fixed-profile chain never had to record it.
--
--   The polynomial factor $(6(N+1))^{45}$ is the usual type-counting slack — $45$ is the number of supported ordered grade triples of the fourth power — and is absorbed downstream by the strict inequality in the value statement.
--
--   *Formalization note.* Since the two profiles share their marginals, the numerators of the two star degrees agree, so the ratio is the reciprocal ratio of the two products of factorials, which by the multinomial identity is the ratio of the two forty-five-cell multinomial coefficients.  Bounding the numerator below and the denominator above by their entropy exponentials, and using that the support entropy of a profile is $\log 3 - \log E$, converts the ratio of multinomials into $(E(b)/E(a))^N$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Equation (3.4) (the infimum over the marginal fibre) and Section 5; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_star_degree_ratio_entropy_lower
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j) :
    (MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB bstar) /
        MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB base)) ^
        (MME.StothersFourth.genOuterLength base m) ≤
      (6 * ((MME.StothersFourth.genOuterLength base m + 1 : ℕ) : ℝ)) ^ 45 *
        ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
          (MME.StothersFourth.genHashTargetStarDegree bstar m : ℝ)) := by
  sorry
