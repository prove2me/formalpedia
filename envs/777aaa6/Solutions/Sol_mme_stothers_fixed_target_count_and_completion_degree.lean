-- Prove2me | solution 1 for mme_stothers_fixed_target_count_and_completion_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:35:19.451882+00:00
-- url     : https://prove2.me/submissions/fe46db59-d4f6-4378-935d-0a4a216f00dc

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_exact_target_count_factorization
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_exact_target_star_degree_le_power100
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_hash_degree_exponential_budget

open MME BigOperators Filter

set_option autoImplicit false
set_option warningAsError true

theorem solution :
    ∀ᶠ m : ℕ in atTop,
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
  filter_upwards [eventually_gt_atTop 0] with m hm
  dsimp only
  have hfactor :=
    MME.StothersFourth.mme_stothers_fixed_exact_target_count_factorization m
  have hdegree :
      ∀ i : Fin 3,
        ∀ a : {a : MME.StothersFourth.FixedMarginalSupportedAddress m //
          MME.StothersFourth.FixedHasExactJointProfile a},
        Nat.card
            {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
              b.1 i = a.1.1 i} ≤
          (6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 100 *
            MME.StothersFourth.fixedHashTargetStarDegree m :=
    fun i a ↦
      MME.StothersFourth.mme_stothers_fixed_exact_target_star_degree_le_power100
        m hm i a
  have hbudget :=
    MME.StothersFourth.mme_stothers_fixed_hash_degree_exponential_budget m hm
  simpa only
      [MME.StothersFourth.fixedHashTargetStarDegree,
        MME.StothersFourth.fixedHashTargetJointTable] using
    And.intro hfactor.1
      (And.intro hfactor.2 (And.intro hdegree hbudget))
