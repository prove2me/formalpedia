-- Prove2me | solution 2 for mme_dwz_fourth_fixed_tau_value_surplus
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T18:19:44.771836+00:00
-- url     : https://prove2.me/submissions/7c45ede4-4425-4e50-ab84-7333ab1a5712

import Theorems.Thm_mme_dwz_q5_fourth_value_240101_over_100_of_component_endpoints
import Theorems.Thm_mme_dwz_q5_all_original_profile_component_endpoints
import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] :
    ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5)
        (790643 / 1000000) V  := by
  refine ⟨240101 / 100, by norm_num, ?_⟩
  exact mme_dwz_q5_fourth_value_240101_over_100_of_component_endpoints
    mme_dwz_q5_all_original_profile_component_endpoints
