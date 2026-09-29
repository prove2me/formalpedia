-- Prove2me | Theorems.Thm_mme_stothers_general_profile_rate_below_marginal_multinomial
-- name    : mme_stothers_general_profile_rate_below_marginal_multinomial
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T04:57:33.109786+00:00
-- url     : https://prove2.me/theorems/884d79d1-2766-4a71-9397-8a25f1659b14
-- title:
--   General-profile Equation (5.3) rate bookkeeping
-- statement:
--   **Equation (5.3) rate bookkeeping at an arbitrary integral ten-class profile.**
--
--   Fix an integral witness for the Davie--Stothers ten Table-1 symmetry classes: a vector
--   $(\beta_1,\dots,\beta_{10})$ of strictly positive natural numbers (`base`), its weighted total
--
--   $$D \;=\; \sum_{i=1}^{10} n_i \beta_i \qquad (n_i = \texttt{classMultiplicity}\ i),$$
--
--   the induced normalized profile $a_i = \beta_i / D \in Z$, and the nine integral marginal counts
--   $M_j = (Q\beta)_j$ obtained by applying the Equation (5.2) matrix $Q$ to the *unnormalized* $\beta$.
--   Because $Q$ is linear, $M_j / (3D)$ is exactly the paper's marginal $A_j = \tfrac13 (Qa)_j$, and
--   summing the nine rows of $Q$ gives $\sum_j M_j = 3D$, so $N = 3Dm$ is the address length at scale $m$.
--
--   Then there is a constant $C \ge 0$ such that for all large $m$,
--
--   $$\mathrm{globalRate}(6,\tau,a,a)^{\,3Dm}\cdot e^{-C\sqrt{3Dm+1}}
--   \;\le\;
--   \binom{3Dm}{M_1m,\dots,M_9m}\cdot \prod_{i=1}^{10} v_i(\tau)^{\,n_i \beta_i m}.$$
--
--   In words: at *any* integral profile, the nine-letter marginal multinomial carries the entire
--   scalar part of the global rate of Equation (5.3) that is not already accounted for by the ten
--   Table-1 constituent values $v_i$, up to a single uniform $e^{-C\sqrt N}$ loss which is
--   irrelevant in the laser limit. The two sides are an identity up to Stirling factors: the
--   $\prod_j A_j^{-A_j}$ entropy factor of `globalRate` is exactly the exponential growth rate of the
--   multinomial coefficient, and the $a_i^{a_i} a_i^{-a_i}$ pair inside `globalRate` cancels on the
--   diagonal $b = a$.
--
--   This is the profile-parametric form of the published fixed-witness statement
--   `mme_stothers_fixed_profile_rate_below_marginal_multinomial`, which is recovered verbatim by
--   taking $\beta = (98, 1862, 73075, 1023050, 3626000, 98000, 2156000, 13720000, 21560000, 38710000)$,
--   $D = 97942072$ and
--   $M = (5822170, 31951724, 86288150, 106906100, 56252000, 6358100, 244150, 3724, 98)$.
--   No numerical property of that witness is used: the proof needs only positivity of the ten
--   counts, and it is therefore reusable at every profile appearing in the general Theorem 5.3
--   optimization (and at the different profiles of the DWZ and More-Asymmetry fourth-power tables).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3 (Lemma 3.3 and Equations (3.2)-(3.4)) and Section 5, Equation (5.3); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_general_profile_rate_below_marginal_multinomial
    (tau : ℝ) (a : Fin 10 → ℝ) (base : Fin 10 → ℕ) (marg : Fin 9 → ℕ) (D : ℕ)
    (hbase : ∀ r, 0 < base r)
    (hD : D = ∑ r : Fin 10, MME.StothersFourth.classMultiplicity r * base r)
    (ha : ∀ i, a i = (base i : ℝ) / (D : ℝ))
    (hmarg : ∀ j, (marg j : ℝ) =
      MME.StothersFourth.Q (fun i ↦ (base i : ℝ)) j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        (MME.StothersFourth.globalRate 6 tau a a) ^ (3 * D * m) *
            Real.exp (-C * Real.sqrt (((3 * D * m + 1 : ℕ) : ℝ))) ≤
          (Nat.multinomial Finset.univ (fun j : Fin 9 ↦ marg j * m) : ℝ) *
            (∏ r : Fin 10,
              (MME.StothersFourth.classValue 6 tau r) ^
                (MME.StothersFourth.classMultiplicity r * (base r * m))) := by
  sorry
