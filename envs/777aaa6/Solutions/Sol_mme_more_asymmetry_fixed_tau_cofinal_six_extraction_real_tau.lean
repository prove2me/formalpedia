-- Prove2me | solution 1 for mme_more_asymmetry_fixed_tau_cofinal_six_extraction_real_tau
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T04:35:23.459003+00:00
-- url     : https://prove2.me/submissions/22631f1e-aeac-4ab2-b98d-489635c84870
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions
import Theorems.Thm_mme_more_asymmetry_six_symmetric_tau_value_surplus

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] :
    ∃ V : ℝ, (2401 : ℝ) < V ∧
      ∃ (s : ℕ → ℕ) (error : ℕ → ℝ),
        Tendsto s atTop atTop ∧
        Tendsto error atTop (nhds 0) ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ (k : ℕ) (a b c : Fin k → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
              ((sixSymmetrization
                (MME.StothersFourth.cwFourthObj K 5)).kronPow (s n)) ∧
              (V ^ (6 : ℕ)) ^ (s n) * (1 - error n) ≤
              ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^
                ((3952233 : ℝ) / 5000000)) := by
  obtain ⟨V, hV, hscalar⟩ :=
    mme_more_asymmetry_six_symmetric_tau_value_surplus (K := K)
  obtain ⟨s, error, hs, herror, _hpositive, hextract⟩ :=
    mme_HasTauValueAtLeast_to_cofinal_finite_extractions
      (T := sixSymmetrization (MME.StothersFourth.cwFourthObj K 5))
      (tau := ((3952233 : ℝ) / 5000000))
      (V := V ^ (6 : ℕ)) hscalar
  exact ⟨V, hV, s, error, hs, herror, Filter.Eventually.of_forall hextract⟩
