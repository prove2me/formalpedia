-- Prove2me | Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum
-- name    : BanditAlgorithm.integrable_discountedStoppedSum
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:01:28.768873+00:00
-- url     : https://prove2.me/theorems/b2b0c36a-be4b-47a9-9018-f878f8b6b321
-- title:
--   Integrability of stopped discounted rewards
-- statement:
--   Under Assumption 35.6, every discounted reward sum stopped at an adapted stopping time is integrable. Pathwise, its absolute value is dominated by the full discounted absolute-reward series.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Assumption 35.6 and the discounted retirement game, printed pp.448--449.

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.integrable_discountedStoppedSum
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum α r τ) (markovChainMeasure P x) := by
  sorry
