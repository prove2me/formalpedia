-- Prove2me | Theorems.Thm_BanditAlgorithm_measurable_gittinsFiniteRetirementValue
-- name    : BanditAlgorithm.measurable_gittinsFiniteRetirementValue
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:12:25.213678+00:00
-- url     : https://prove2.me/theorems/09839dc7-6f05-4ed1-a51d-6c8c818ae298
-- title:
--   Measurability of finite-horizon Gittins Bellman values
-- statement:
--   Every finite-horizon Bellman value function for the discounted retirement game is measurable. The proof inducts on the horizon, using measurability of integration against a probability kernel.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 35.3 (Wald--Bellman equation), printed pp.442--443, specialized to the discounted retirement game used in Lemma 35.7 on printed p.449.

import Definitions.Def_GittinsFiniteRetirementValue

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.measurable_gittinsFiniteRetirementValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) :
    ∀ n, Measurable (gittinsFiniteRetirementValue P r α γ n) := by
  sorry
