-- Prove2me | Theorems.Thm_mme_stothers_general_profile_outer_capacity_stationary
-- name    : mme_stothers_general_profile_outer_capacity_stationary
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T05:06:35.77234+00:00
-- url     : https://prove2.me/theorems/00752dee-8c6a-4fe4-a790-1f1574337aca
-- title:
--   Outer capacity of a general profile against a stationary partner
-- statement:
--   **The outer capacity of a general profile, with the combination loss made explicit.**
--
--   Let $\beta$ and $\beta^{*}$ be strictly positive integral ten-class profiles with the same nine-grade marginals, let the normalised partner $b = \beta^{*}/D$ be stationary, $b \in \mathcal N$, and fix an exponent $\tau$.  Write $a = \beta/D$ for the normalised profile, $N = 3Dm$ for the address length, $v_r(\tau)$ for the ten class values, and $\Delta_\gamma(m)$ for the star degree of $\gamma$ on the marginal fibre.
--
--   Then there is a constant $C \ge 0$ such that for all large $m$ there is a mode-disjoint family $F$ of exact outer addresses of profile $\beta$ with
--
--   $$G(\tau,a)^{N} \cdot \frac{\Delta_\beta(m)}{\bigl(6(N+1)\bigr)^{100}\,\Delta_{\beta^{*}}(m)} \cdot e^{-C\sqrt{N+1}} \;\le\; \#F \cdot \prod_{r=1}^{10} v_r(\tau)^{\,c_r \beta_r m},$$
--
--   where $G(\tau,a)$ is the global rate of the profile $a$ against itself.
--
--   This is the general-profile form of the outer capacity that feeds the fourth-power value assembly.  Compared with the published fixed-profile statement it carries one extra factor, the ratio of the two star degrees.  That factor is the *combination loss* of Equation (3.4): the exact-profile targets of $\beta$ are counted by $\Delta_\beta$, but the completion star whose degree Behrend's construction must beat is governed by the maximum-entropy profile $\beta^{*}$ on the same marginal fibre.  On the diagonal $\beta = \beta^{*}$ the ratio is $1$ and one recovers the published statement; off the diagonal the ratio is exponentially small in $N$, and it is exactly this loss that Davie--Stothers record as an infimum over the marginal fibre.  Making it explicit is what allows the profile to be optimised, since the fixed chain, living only on the diagonal, could never see it.
--
--   *Formalization note.* The proof combines the Stirling-level rate bound relating $G(\tau,a)^{N}$ to the marginal multinomial times the class-value product with the partner-corrected count of the surviving mode-disjoint family; the two error constants add.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Equations (3.2)-(3.4), and Section 5; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_general_profile_outer_capacity_stationary
    (base bstar : Fin 10 → ℕ) (tau : ℝ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N := MME.StothersFourth.genOuterLength base m
        ∃ F : Finset (MME.StothersFourth.GenExactOuterAddress base m),
          MME.StothersFourth.GenInducedModeDisjoint F ∧
          (MME.StothersFourth.globalRate 6 tau
                (MME.StothersFourth.genProfileB base)
                (MME.StothersFourth.genProfileB base)) ^ N *
              ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
                (((6 * (N + 1)) ^ 100 *
                  MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ)) *
              Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) *
              (∏ r : Fin 10,
                (MME.StothersFourth.classValue 6 tau r) ^
                  (MME.StothersFourth.classMultiplicity r *
                    MME.StothersFourth.genProfileCount base m r)) := by
  sorry
