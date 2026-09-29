-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_cofinal_finite_extraction_core_v2
-- name    : mme_stothers_phi233_cyclic_cofinal_finite_extraction_core_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T00:25:40.341725+00:00
-- url     : https://prove2.me/theorems/912fcb0e-b791-4f55-ad08-fcb1037d943a
-- title:
--   Davie--Stothers phi_233 cofinal finite extraction core
-- statement:
--   The cofinal finite extraction required for the literal phi_233 constituent: every value strictly below the class-9 rate is witnessed along an unbounded sequence of tensor powers by finite restrictions whose weighted rank sum approaches the target from below.
-- source:
--   Davie--Stothers, Lemma 5.1(v), literal phi_233 constituent and finite extraction interface.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_cofinal_finite_extraction_core_v2
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (V : ℝ) (hV : 0 ≤ V)
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
