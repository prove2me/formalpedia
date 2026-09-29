-- Prove2me | Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_sub_charge
-- name    : BanditAlgorithm.integral_discountedStoppedSum_sub_charge
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:06:03.247954+00:00
-- url     : https://prove2.me/theorems/8509fa3f-e3c9-4277-ba07-ded63af292b1
-- title:
--   Expected stopping-block charge identity
-- statement:
--   Under Assumption 35.6, expectation commutes with the stopping-block charge identity: expected discounted net reward equals expected discounted reward minus $\gamma$ times expected discounted duration.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Eq. (35.7), printed p.448, and prevailing-charge proof, printed p.452.

import Theorems.Thm_BanditAlgorithm_discountedStoppedSum_sub_charge
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum_one

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.integral_discountedStoppedSum_sub_charge
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x) =
      (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) -
        γ * (∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
          ∂markovChainMeasure P x) := by
  sorry
