-- Prove2me | Theorems.Thm_mme_stothers_general_outer_hash_budget_of_bounded_degree_data
-- name    : mme_stothers_general_outer_hash_budget_of_bounded_degree_data
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T17:28:27.319023+00:00
-- url     : https://prove2.me/theorems/4649f6be-4dd1-4826-b47c-25f84f5cafc8
-- title:
--   Outer hash budget with a separated star degree
-- statement:
--   **Outer hash budget when the star degree is controlled by a second, larger degree.**
--
--   Fix a strictly positive integral ten-class profile $\beta$ and two scale-indexed naturals
--   $d_m \le \Delta_m$. Suppose for all large $m$, with $N = 3Dm$ and $V = N!/\prod_j M_j!$:
--
--   - the exact-profile targets number exactly $V d_m$, with $1\le d_m$;
--   - every completion star has at most $(6(N+1))^{100}\Delta_m$ members;
--   - $(6(N+1))^{100}\Delta_m \le 5^{1000N}$.
--
--   Then for all large $m$ some affine hash state retains a vertex-closed family $E$ with
--
--   $$\#\{\text{collisions in }E\} \;+\; V\,\frac{d_m}{\Delta_m}\,e^{-10^{6}\sqrt{N+1}}
--   \;\le\; \#\{\text{targets in }E\}.$$
--
--   The point of separating the two degrees is Equation (3.4). In the general Theorem 5.3 the target
--   count is governed by the star degree $D_*(\beta)$ of the profile itself, while the *bound* on a
--   completion star is governed by $D_*(\beta^{*})$ for the maximum-entropy profile on the same marginal
--   fibre, and these differ. Taking $d_m = D_*(\beta)$ and $\Delta_m = D_*(\beta^{*})$, the retained
--   family carries the ratio $d_m/\Delta_m = \bigl(\mathcal E(\beta^{*})/\mathcal E(\beta)\bigr)^{N}$ --
--   precisely the combination loss. On the diagonal $\beta = \beta^{*}$ the ratio is $1$ and the
--   statement collapses to the fixed-witness form.
--
--   The parameter selection is unchanged and profile-independent; only the bookkeeping of which degree
--   enters where has to be tracked.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equation (3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_general_outer_hash_budget_of_bounded_degree_data
    (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r)
    (Dsmall Dbig : ℕ → ℕ)
    (hdata : ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((MME.StothersFourth.genMarginalCount base m j).factorial : ℝ)
      (Nat.card
          {a : MME.StothersFourth.GenMarginalSupportedAddress base m //
            MME.StothersFourth.GenHasExactJointProfile a} : ℝ) = V * (Dsmall m : ℝ) ∧
        1 ≤ Dsmall m ∧ Dsmall m ≤ Dbig m ∧
        (∀ i : Fin 3,
          ∀ a : {a : MME.StothersFourth.GenMarginalSupportedAddress base m //
            MME.StothersFourth.GenHasExactJointProfile a},
          Nat.card
            {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
              b.1 i = a.1.1 i} ≤ (6 * (N + 1)) ^ 100 * Dbig m) ∧
        (6 * (N + 1)) ^ 100 * Dbig m ≤ 5 ^ (1000 * N)) :
    ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((MME.StothersFourth.genMarginalCount base m j).factorial : ℝ)
      ∃ E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m),
        MME.StothersFourth.GenMarginalVertexClosed E ∧
        ((MME.StothersFourth.genTargetAmbientCollisions E).card : ℝ) +
            V * ((Dsmall m : ℝ) / (Dbig m : ℝ)) *
              Real.exp
                (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((MME.StothersFourth.genExactTargetEdges E).card : ℝ) := by
  sorry
