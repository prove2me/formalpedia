-- Prove2me | Theorems.Thm_mme_stothers_phi233_finite_extraction_tau_le_eight
-- name    : mme_stothers_phi233_finite_extraction_tau_le_eight
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T08:33:34.154973+00:00
-- url     : https://prove2.me/theorems/8552412f-a488-4dbf-a356-98416e6a0093
-- title:
--   Cofinal finite extraction for the q6 Stothers 233 constituent at all exponents up to eight
-- statement:
--   Let $K$ be a field, let $\tau\le8$, and let $T$ be the cyclic symmetrization of the $(2,3,3)$ constituent of the fourth power of the Coppersmith–Winograd tensor at $q=6$. For every $0\le V<\operatorname{classValue}(6,\tau,9)$, there are integers $s_n\to\infty$ and real losses $\ell_n\to0$ such that, for all sufficiently large $n$, $T^{\otimes s_n}$ restricts to a finite direct sum of matrix multiplication tensors of dimensions $(a_i,b_i,c_i)$ satisfying
--   $$V^{s_n}(1-\ell_n)\le\sum_i(a_i b_i c_i)^\tau.$$
--   This extends the finite-extraction bound throughout the exponent range up to eight, including negative exponents.
-- source:
--   The scalar bound below two thirds and the generalized ordered-profile surplus, whose order hypotheses hold through exponent eight.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value
open MME BigOperators Filter
universe u
set_option autoImplicit false

theorem mme_stothers_phi233_finite_extraction_tau_le_eight
    {K : Type u} [Field K] (tau : ℝ) (htau : tau ≤ 8) (V : ℝ) (hV : 0 ≤ V)
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
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)  := by sorry
