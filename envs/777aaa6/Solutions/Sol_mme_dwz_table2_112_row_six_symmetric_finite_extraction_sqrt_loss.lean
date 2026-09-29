-- Prove2me | solution 1 for mme_dwz_table2_112_row_six_symmetric_finite_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T19:44:34.282705+00:00
-- url     : https://prove2.me/submissions/1194b4ce-d294-442a-85c7-3804ecf3c3c0

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_q6_112_primary_hash_family_restricted_component_Ctensor_certificate
import Theorems.Thm_mme_dwz_q6_112_restricted_primary_certificates_to_six_symmetric_finite_rate

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (Cdim j)))
            (sixSymmetrization
              (restrictedComponentPower K (12 : Fin 15) m)) ∧
          (((componentBase tau (12 : Fin 15)) ^
              (MME.DWZTable2Counts.component (12 : Fin 15) * m)) ^ (6 : ℕ)) *
              Real.exp (-C * Real.sqrt
                (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  apply
    mme_dwz_q6_112_restricted_primary_certificates_to_six_symmetric_finite_rate
      tau htau
  intro m A H family
  exact
    mme_dwz_q6_112_primary_hash_family_restricted_component_Ctensor_certificate
      (K := K) m A H family
