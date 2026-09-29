-- Prove2me | Theorems.Thm_mme_stothers_general_bounded_degree_data
-- name    : mme_stothers_general_bounded_degree_data
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T02:58:49.564211+00:00
-- url     : https://prove2.me/theorems/231aff02-88c1-4b0a-a7ef-ad1dd50af203
-- title:
--   Degree data against a stationary partner profile
-- statement:
--   **The degree data of a general profile against a stationary partner.**
--
--   Fix two strictly positive integral ten-class profiles $\beta$ and $\beta^{*}$ with the same
--   nine-grade marginals, and suppose every $45$-cell histogram on that marginal fibre has conditional
--   entropy at most $\beta^{*}$'s. Then for all large scales $m$, with $N = 3Dm$ and
--   $V = N!/\prod_j M_j!$:
--
--   - the exact-profile targets of $\beta$ number exactly $V\,D_*(\beta)$, with $D_*(\beta)\ge1$;
--   - $D_*(\beta)\;\le\;(6(N+1))^{100}D_*(\beta^{*})$;
--   - every completion star has at most $(6(N+1))^{100}\cdot\bigl[(6(N+1))^{100}D_*(\beta^{*})\bigr]$
--     members;
--   - and $(6(N+1))^{100}\cdot\bigl[(6(N+1))^{100}D_*(\beta^{*})\bigr] \le 5^{1000N}$.
--
--   This is exactly the input shape of the outer hash budget with separated degrees, taken at
--   $d_m = D_*(\beta)$ and $\Delta_m = (6(N+1))^{100}D_*(\beta^{*})$. The polynomial cushion in
--   $\Delta_m$ is what makes the comparison $d_m\le\Delta_m$ unconditional: the two star degrees are
--   comparable only up to a polynomial factor, since entropy maximality is an asymptotic statement, and
--   the cushion absorbs that. It costs nothing downstream, being swallowed by the
--   $e^{-c\sqrt N}$ loss.
--
--   Since the two profiles share their marginals they also share $D$ and hence the address length,
--   which is what lets the two sides be compared at the same scale.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Data.Nat.Factorial.NatCast

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_general_bounded_degree_data
    (base bstar : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j = MME.StothersFourth.genMarginalBaseCount base j)
    (hcond : ∀ (m : ℕ) (k : MME.StothersFourth.GenHashJointMultiplicityTable),
      (∀ l : Fin 3, ∀ j : Fin 9,
        (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 l = j},
          k sigma.1) = MME.StothersFourth.genMarginalCount base m j) →
      ∀ i : Fin 3,
      (∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
            (k sigma.1 : ℝ) / (MME.StothersFourth.genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
            (MME.StothersFourth.genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ))) :
    ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((MME.StothersFourth.genMarginalCount base m j).factorial : ℝ)
      (Nat.card
          {a : MME.StothersFourth.GenMarginalSupportedAddress base m //
            MME.StothersFourth.GenHasExactJointProfile a} : ℝ) =
          V * (MME.StothersFourth.genHashTargetStarDegree base m : ℝ) ∧
        1 ≤ MME.StothersFourth.genHashTargetStarDegree base m ∧
        MME.StothersFourth.genHashTargetStarDegree base m ≤
          (6 * (N + 1)) ^ 100 * MME.StothersFourth.genHashTargetStarDegree bstar m ∧
        (∀ i : Fin 3,
          ∀ a : {a : MME.StothersFourth.GenMarginalSupportedAddress base m //
            MME.StothersFourth.GenHasExactJointProfile a},
          Nat.card
            {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
              b.1 i = a.1.1 i} ≤
            (6 * (N + 1)) ^ 100 *
              ((6 * (N + 1)) ^ 100 * MME.StothersFourth.genHashTargetStarDegree bstar m)) ∧
        (6 * (N + 1)) ^ 100 *
            ((6 * (N + 1)) ^ 100 * MME.StothersFourth.genHashTargetStarDegree bstar m) ≤
          5 ^ (1000 * N) := by
  sorry
