-- Prove2me | Theorems.Thm_mme_stothers_general_outer_hash_budget_stationary
-- name    : mme_stothers_general_outer_hash_budget_stationary
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T05:00:19.300318+00:00
-- url     : https://prove2.me/theorems/ecfb3919-42bd-4f77-a174-2b989023a74b
-- title:
--   Outer hash budget of a general profile against a stationary partner
-- statement:
--   **The affine-hash budget for a general profile, paid at the partner's star degree.**
--
--   Let $\beta$ and $\beta^{*}$ be strictly positive integral ten-class profiles with the same nine-grade marginals, and suppose the normalised partner $b = \beta^{*}/D$ is stationary, $b \in \mathcal N$.  Write $N = 3Dm$ for the address length, $V = N! / \prod_j \bigl((Q\beta)_j m\bigr)!$ for the number of marginally supported mode words, and
--
--   $$\Delta_\gamma(m) \;=\; \frac{\prod_j \bigl((Q\beta)_j m\bigr)!}{\prod_\sigma \mu_\gamma(m,\sigma)!}$$
--
--   for the star degree of a profile $\gamma$ on that marginal fibre.  Then for all large $m$ there is a vertex-closed family $E$ of marginally supported addresses with
--
--   $$\#\,\mathrm{collisions}(E) \;+\; V \cdot \frac{\Delta_\beta(m)}{\bigl(6(N+1)\bigr)^{100}\,\Delta_{\beta^{*}}(m)} \cdot e^{-10^{6}\sqrt{N+1}} \;\le\; \#\,\mathrm{exactTargetEdges}(E) .$$
--
--   The point is the ratio $\Delta_\beta / \Delta_{\beta^{*}}$.  The exact-profile targets of $\beta$ number $V \Delta_\beta(m)$, but the degree of the completion star is controlled by the *maximum-entropy* profile on the marginal fibre, which is $\beta^{*}$, not $\beta$.  Behrend's construction must therefore be run at the larger degree $\Delta_{\beta^{*}}$, and the retained family carries only the fraction $\Delta_\beta/\Delta_{\beta^{*}}$ of the targets.  On the diagonal $\beta = \beta^{*}$ the ratio is $1$ and this reduces to the published fixed-profile budget; off the diagonal it is the combination loss that Equation (3.4) of Davie--Stothers records as an infimum over the marginal fibre.
--
--   The polynomial factor $(6(N+1))^{100}$ is the slack in the star-degree comparison and is sub-exponential, so it is absorbed downstream in the same way as the Behrend factor $e^{-10^{6}\sqrt{N+1}}$.
--
--   *Formalization note.* The result is the abstract bounded-degree budget instantiated at $\Delta_{\mathrm{small}} = \Delta_\beta$ and $\Delta_{\mathrm{big}} = (6(N+1))^{100}\Delta_{\beta^{*}}$, with the degree data supplied by the stationarity of $b$ through the conditional-entropy comparison.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_general_outer_hash_budget_stationary
    (base bstar : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((MME.StothersFourth.genMarginalCount base m j).factorial : ℝ)
      ∃ E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m),
        MME.StothersFourth.GenMarginalVertexClosed E ∧
        ((MME.StothersFourth.genTargetAmbientCollisions E).card : ℝ) +
            V * ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
                  (((6 * (N + 1)) ^ 100 *
                    MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ)) *
              Real.exp
                (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((MME.StothersFourth.genExactTargetEdges E).card : ℝ) := by
  sorry
