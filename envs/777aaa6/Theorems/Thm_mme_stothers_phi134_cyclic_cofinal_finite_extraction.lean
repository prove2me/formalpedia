-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_cofinal_finite_extraction
-- name    : mme_stothers_phi134_cyclic_cofinal_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:04:26.242384+00:00
-- url     : https://prove2.me/theorems/0592d02a-7304-45b1-8e69-a8320c176173
-- title:
--   Davie–Stothers phi_134: source-faithful cofinal finite extraction
-- statement:
--   Let K be a field and let 2 ≤ 3 tau ≤ 3. For every nonnegative base V strictly below the Davie–Stothers endpoint R_134 = 4(E+L)(2+2E+H), there are cofinal tensor powers and losses tending to zero such that the corresponding power of the cyclic symmetrization of the literal phi_134 constituent restricts to a finite direct sum of matrix-multiplication tensors of tau-weight at least V to that power times one minus the loss. This is the finite, source-faithful form of Lemma 5.1(iii); unlike the circular aggregate reductions currently present in the graph, it must be proved from the eight literal fine components, the injective-marginal type-2 hash extraction, and the displayed optimizer profile.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), printed p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_cofinal_finite_extraction
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 7) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
