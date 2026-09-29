-- Prove2me | Theorems.Thm_mme_stothers_fixed_target_count_and_completion_degree
-- name    : mme_stothers_fixed_target_count_and_completion_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:09:55.555747+00:00
-- url     : https://prove2.me/theorems/50656da1-c21b-41ee-beb7-7d3e18096e18
-- title:
--   Fixed-profile target count and subexponential completion degree
-- statement:
--   At every sufficiently large exact scale, let $V_m$ be the multinomial number of words with the fixed nine-grade marginal and let $D_m^*$ be the exact number of target-table completions of one fixed coordinate word. Then the total exact-profile target count is exactly $V_mD_m^*$ and $D_m^*$ is positive. Moreover every completion star in any of the three coordinate modes has degree at most
--
--   $$D_m=(6(N_m+1))^{100}D_m^*,$$
--
--   and this deliberately loose degree satisfies $D_m ≤ 5^{1000N_m}$.
--
--   Thus the fixed maximum-entropy joint table controls every competing completion table up to a polynomial factor. This is the exact enumerative input needed by the affine Salem--Spencer hash budget; it contains no hashing or tensor-value assertion.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Equations (3.2)--(3.3), Lemma 5.2, and the fixed stationary profile of Section 5. The polynomial factor comes from enumerating the 45-cell joint histograms and applying multinomial entropy bounds.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_stothers_fixed_outer_profile

open BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_fixed_target_count_and_completion_degree :
    ∀ᶠ m : ℕ in Filter.atTop,
      let N := MME.StothersFourth.fixedOuterLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9,
            ((MME.StothersFourth.fixedMarginalCount m j).factorial : ℝ)
      let Dstar : ℕ :=
        (∏ j : Fin 9,
          (MME.StothersFourth.fixedMarginalCount m j).factorial) /
        ∏ sigma : {sigma : Fin 3 → Fin 9 //
            (∑ s, (sigma s).val) = 8},
          (MME.StothersFourth.fixedJointMultiplicity m sigma.1).factorial
      let P := (6 * (N + 1)) ^ 100
      let D := P * Dstar
      (Nat.card
          {a : MME.StothersFourth.FixedMarginalSupportedAddress m //
            MME.StothersFourth.FixedHasExactJointProfile a} : ℝ) =
          V * (Dstar : ℝ) ∧
        1 ≤ Dstar ∧
        (∀ i : Fin 3,
          ∀ a : {a : MME.StothersFourth.FixedMarginalSupportedAddress m //
            MME.StothersFourth.FixedHasExactJointProfile a},
          Nat.card
            {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
              b.1 i = a.1.1 i} ≤ D) ∧
        D ≤ 5 ^ (1000 * N) := by
  sorry
