-- Prove2me | solution 1 for BanditAlgorithm.gittins_index_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T19:56:10.071535+00:00
-- url     : https://prove2.me/submissions/1f57efbb-52bc-4a62-8b9d-67d12cf15544

import Theorems.Thm_BanditAlgorithm_gittins_index_policy_dominates

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

theorem solution {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (πstar : MarkovBanditPolicy k S) (hπ : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) :
    markovBanditDiscountedValue P r α πstar x =
      ⨆ π : MarkovBanditPolicy k S, markovBanditDiscountedValue P r α π x := by
  have hdom := gittins_index_policy_dominates
    P hr hα0 hα1 hint πstar hπ x
  letI : Nonempty (MarkovBanditPolicy k S) := ⟨πstar⟩
  have hbdd : BddAbove
      (Set.range fun π : MarkovBanditPolicy k S ↦
        markovBanditDiscountedValue P r α π x) := by
    refine ⟨markovBanditDiscountedValue P r α πstar x, ?_⟩
    rintro y ⟨π, rfl⟩
    exact hdom π
  apply le_antisymm
  · exact le_ciSup hbdd πstar
  · exact ciSup_le hdom
