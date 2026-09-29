-- Prove2me | Theorems.Thm_mme_stothers_phi233_finite_extraction_from_zeroing_v3
-- name    : mme_stothers_phi233_finite_extraction_from_zeroing_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T06:45:57.506626+00:00
-- url     : https://prove2.me/theorems/d9dbb873-bd90-4ab1-a45c-4649f95ad5d2
-- title:
--   Finite Phi233 extraction from induced-word zeroing
-- statement:
--   A reusable interface for the phi233 constituent: induced-word zeroing and collision pruning convert a cofinal witness into frequent direct-sum matrix-multiplication extractions with vanishing loss.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Section 5, Lemma 5.1; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value
open MME BigOperators Filter
universe u
set_option autoImplicit false

theorem mme_stothers_phi233_finite_extraction_from_zeroing_v3
    {K : Type u} [Field K] (tau : ℝ) (V : ℝ) (hV : 0 ≤ V)
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
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
