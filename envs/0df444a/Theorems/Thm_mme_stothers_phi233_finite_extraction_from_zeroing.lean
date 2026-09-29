-- Prove2me | Theorems.Thm_mme_stothers_phi233_finite_extraction_from_zeroing
-- name    : mme_stothers_phi233_finite_extraction_from_zeroing
-- status  : Open
-- author  : @WillR
-- created : 2026-09-05T06:38:16.676739+00:00
-- url     : https://prove2.me/theorems/fc00a74a-4fbc-472b-b30f-09b67c9e2e1e
-- title:
--   Finite Phi233 extraction from induced-word zeroing
-- statement:
--   This interface isolates the finite-extraction core for the $\varphi_{233}$ constituent. For a nonnegative threshold $V$ strictly below the ninth class value, the induced-word zeroing construction and its finite collision-pruning argument produce a sequence of tensor powers tending to infinity, losses tending to zero, and frequent direct-sum matrix-multiplication witnesses whose weighted volumes dominate $V$ to the relevant power. The interface is the reusable bridge from the exact address factorization and zeroing data to the asymptotic tau-value conclusion.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Lemma 5.1 and the induced-word zeroing extraction for phi233; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_finite_extraction_from_zeroing
    {K : Type u} [Field K] (tau : ℝ) (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 9) :
    ∃ (s : ℕ → ℕ) (loss : ℝ → ℝ),
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
