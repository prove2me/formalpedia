-- Prove2me | Theorems.Thm_mme_stothers_fixed_profile_rate_below_marginal_multinomial
-- name    : mme_stothers_fixed_profile_rate_below_marginal_multinomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:01:50.162642+00:00
-- url     : https://prove2.me/theorems/b1bd51ac-ffb8-48d8-a32c-d6bf5112c356
-- title:
--   Fixed Stothers rate from its exact marginal multinomial
-- statement:
--   For every real tau, the exact fixed-profile Stothers global rate at scale m is bounded by the product of the exact nine-coordinate marginal multinomial and the ten exact constituent powers, up to one uniform exp(-C sqrt(N+1)) factor. The constant C is independent of m and tau. This is the complete analytic and scalar part of the fixed outer-capacity estimate; only constructing a sufficiently large induced family remains combinatorial.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Equations (5.2)--(5.3), together with the standard multinomial entropy estimate.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_fixed_outer_profile
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_fixed_profile_rate_below_marginal_multinomial
    (tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        (MME.StothersFourth.globalRate 6 tau
              MME.StothersFourth.fixedProfileB
              MME.StothersFourth.fixedProfileB) ^
              (MME.StothersFourth.fixedOuterLength m) *
            Real.exp
              (-C * Real.sqrt
                (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
          (Nat.multinomial Finset.univ
              (fun j : Fin 9 ↦
                MME.StothersFourth.fixedMarginalBaseCount j * m) : ℝ) *
            (∏ r : Fin 10,
              (MME.StothersFourth.classValue 6 tau r) ^
                (MME.StothersFourth.classMultiplicity r *
                  MME.StothersFourth.fixedProfileCount m r)) := by
  sorry
