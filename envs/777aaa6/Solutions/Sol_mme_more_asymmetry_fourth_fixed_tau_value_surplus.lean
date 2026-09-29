-- Prove2me | solution 1 for mme_more_asymmetry_fourth_fixed_tau_value_surplus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T08:02:25.801734+00:00
-- url     : https://prove2.me/submissions/a271dd0c-2b98-4ed2-869f-c00becbd60ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_more_asymmetry_fixed_tau_cofinal_six_extraction_real_tau
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] :
    ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5)
        (3952233 / 5000000) V := by
  obtain ⟨V, hV, hdata⟩ :=
    mme_more_asymmetry_fixed_tau_cofinal_six_extraction_real_tau (K := K)
  obtain ⟨s, error, hs, herror, hextract⟩ := hdata
  have hV0 : 0 ≤ V := by
    nlinarith
  have hV6 : 0 ≤ V ^ (6 : ℕ) := pow_nonneg hV0 _
  refine ⟨V, hV, ?_⟩
  unfold HasSixSymmetricTauValueAtLeast
  exact mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (sixSymmetrization (MME.StothersFourth.cwFourthObj K 5))
    (3952233 / 5000000) (V ^ (6 : ℕ)) hV6 s hs error herror hextract
