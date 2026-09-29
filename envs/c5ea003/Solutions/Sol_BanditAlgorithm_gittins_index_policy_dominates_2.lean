-- Prove2me | solution 2 for BanditAlgorithm.gittins_index_policy_dominates
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T17:25:45.993272+00:00
-- url     : https://prove2.me/submissions/49f769fb-58b6-435a-b926-3ebad65654ac

import Theorems.Thm_BanditAlgorithm_gittins_finite_reward_le_index_policy_add_terminal
import Theorems.Thm_BanditAlgorithm_tendsto_gittins_terminal_retirement_potential_zero
import Theorems.Thm_BanditAlgorithm_summable_discounted_markovBanditRoundReward

open MeasureTheory ProbabilityTheory ENNReal

theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α)
    (πstar : BanditAlgorithm.MarkovBanditPolicy k S)
    (hπ : BanditAlgorithm.IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) :
    ∀ π : BanditAlgorithm.MarkovBanditPolicy k S,
      BanditAlgorithm.markovBanditDiscountedValue P r α π x ≤
        BanditAlgorithm.markovBanditDiscountedValue P r α πstar x := by
  intro π
  have hsπ := BanditAlgorithm.summable_discounted_markovBanditRoundReward
    P hr hα0 hα1 hint π x
  have hsstar := BanditAlgorithm.summable_discounted_markovBanditRoundReward
    P hr hα0 hα1 hint πstar x
  have htail :=
    BanditAlgorithm.tendsto_gittins_terminal_retirement_potential_zero
      P hr hα0 hα1 hint πstar x
  have hleft : Filter.Tendsto (fun N ↦
      ∑ n ∈ Finset.range N,
        α ^ n * BanditAlgorithm.markovBanditRoundReward P r π x n)
      Filter.atTop
        (nhds (BanditAlgorithm.markovBanditDiscountedValue P r α π x)) := by
    simpa [BanditAlgorithm.markovBanditDiscountedValue] using
      hsπ.hasSum.tendsto_sum_nat
  have hright : Filter.Tendsto (fun N ↦
      (∑ n ∈ Finset.range N,
        α ^ n * BanditAlgorithm.markovBanditRoundReward P r πstar x n) +
      α ^ N * BanditAlgorithm.markovBanditExpectedRetirementPotential
        P r α πstar x N)
      Filter.atTop
        (nhds (BanditAlgorithm.markovBanditDiscountedValue P r α πstar x)) := by
    simpa [BanditAlgorithm.markovBanditDiscountedValue] using
      hsstar.hasSum.tendsto_sum_nat.add htail
  exact le_of_tendsto_of_tendsto' hleft hright
    (fun N ↦
      BanditAlgorithm.gittins_finite_reward_le_index_policy_add_terminal
        P hr hα0 hα1 hint π πstar hπ x N)
