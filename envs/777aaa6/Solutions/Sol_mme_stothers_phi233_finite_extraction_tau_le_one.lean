-- Prove2me | solution 1 for mme_stothers_phi233_finite_extraction_tau_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T08:31:28.007825+00:00
-- url     : https://prove2.me/submissions/3f0b9df2-b433-44bf-8ae5-063ea8f13634

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value
import Mathlib.Tactic
import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions
import Theorems.Thm_mme_stothers_phi233_below_two_thirds_value_below
import Theorems.Thm_mme_stothers_phi233_cyclic_cofinal_finite_extraction_core_v2

open MME BigOperators Filter
universe u
set_option autoImplicit false

/-- Cofinal finite extraction throughout the full exponent range up to one. -/
theorem solution
    {K : Type u} [Field K] (tau : ℝ) (htau : tau ≤ 1) (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 9) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)  := by
  by_cases hlower : 3 * tau ≤ 2
  · have hv := mme_stothers_phi233_below_two_thirds_value_below
      (K := K) tau V hlower hV hVlt
    obtain ⟨s, loss, hs, hloss, _, hfinite⟩ :=
      mme_HasTauValueAtLeast_to_cofinal_finite_extractions _ tau V hv
    exact ⟨s, loss, hs, hloss, Filter.Eventually.of_forall hfinite⟩
  · exact mme_stothers_phi233_cyclic_cofinal_finite_extraction_core_v2
      tau (by linarith) (by linarith) V hV hVlt

