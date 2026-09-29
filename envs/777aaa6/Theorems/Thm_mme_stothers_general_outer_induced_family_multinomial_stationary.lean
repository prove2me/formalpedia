-- Prove2me | Theorems.Thm_mme_stothers_general_outer_induced_family_multinomial_stationary
-- name    : mme_stothers_general_outer_induced_family_multinomial_stationary
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T05:03:15.213365+00:00
-- url     : https://prove2.me/theorems/2830cce7-c917-4655-90f9-60a78aee2d3b
-- title:
--   Induced mode-disjoint family of a general profile, at the partner-corrected rate
-- statement:
--   **The surviving family of exact outer addresses, counted for a general profile.**
--
--   Let $\beta$ and $\beta^{*}$ be strictly positive integral ten-class profiles with the same nine-grade marginals, and let the normalised partner $b = \beta^{*}/D$ be stationary, $b \in \mathcal N$.  Write $N = 3Dm$ and let $\Delta_\gamma(m)$ denote the star degree of a profile $\gamma$ on the marginal fibre of $\beta$ at scale $m$.
--
--   Then for all large $m$ there is a family $F$ of exact outer addresses of profile $\beta$ whose induced mode words are pairwise disjoint and whose size satisfies
--
--   $$\binom{N}{(Q\beta)_0 m, \dots, (Q\beta)_8 m} \cdot \frac{\Delta_\beta(m)}{\bigl(6(N+1)\bigr)^{100}\,\Delta_{\beta^{*}}(m)} \cdot e^{-10^{6}\sqrt{N+1}} \;\le\; \#F .$$
--
--   This is the output of the hashing step in the form the value assembly consumes: a mode-disjoint family, so that its members can be extracted simultaneously, together with a lower bound on its size at the full multinomial rate, corrected by the ratio of the two star degrees.
--
--   The multinomial is the number of marginally supported mode words; the star-degree ratio is the fraction of the exact-profile targets that survive Behrend pruning, and equals $1$ exactly when $\beta = \beta^{*}$.
--
--   *Formalization note.* The proof combines the affine-hash budget for the pair $(\beta, \beta^{*})$ with the abstract tripartite pruning assembly, which converts a vertex-closed family of marginally supported addresses into a mode-disjoint family of exact addresses at the cost of the ambient collisions that the budget has already paid for.  The identification of the multinomial coefficient with $N!/\prod_j ((Q\beta)_j m)!$ uses that the nine marginal counts sum to $N$, which in turn is the row-sum identity $\sum_j Q_{rj} = 3 c_r$ for the class-marginal matrix.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_general_outer_induced_family_multinomial_stationary
    (base bstar : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.genOuterLength base m
      ∃ F : Finset (MME.StothersFourth.GenExactOuterAddress base m),
        MME.StothersFourth.GenInducedModeDisjoint F ∧
        (Nat.multinomial Finset.univ
            (fun j : Fin 9 ↦ MME.StothersFourth.genMarginalBaseCount base j * m) : ℝ) *
          ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
            (((6 * (N + 1)) ^ 100 *
              MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ)) *
          Real.exp (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤ (F.card : ℝ) := by
  sorry
