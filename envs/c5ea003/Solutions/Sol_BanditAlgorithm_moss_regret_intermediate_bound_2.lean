-- Prove2me | solution 2 for BanditAlgorithm.moss_regret_intermediate_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T07:33:50.830723+00:00
-- url     : https://prove2.me/submissions/6154f927-e266-43b4-9689-97792b32dc42
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BanditAlgorithm_moss_regret_large_gap_occupation_reduction
import Theorems.Thm_BanditAlgorithm_moss_large_gap_occupation_sum_bound

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

theorem solution {k : ℕ} (hk : 0 < k)
    {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditPolicy k} (hπ : IsMOSSPolicy n π) (hkn : k ≤ n) :
    banditRegret ν π n ≤
      24 * Real.sqrt ((k : ℝ) * n) +
        Finset.sum
          (Finset.univ.filter
            (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i))
          (fun i ↦ banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by
  calc
    banditRegret ν π n ≤
        24 * Real.sqrt ((k : ℝ) * n) +
          Finset.sum
            (Finset.univ.filter
              (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i))
            (fun i ↦ banditGap ν i *
              MeasureTheory.integral (banditMeasure ν π n)
                (fun h ↦ (armPullCount i h : ℝ))) :=
      moss_regret_large_gap_occupation_reduction hk hν hπ hkn
    _ ≤
        24 * Real.sqrt ((k : ℝ) * n) +
          Finset.sum
            (Finset.univ.filter
              (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i))
            (fun i ↦ banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by
      simpa [add_comm] using
        (add_le_add_left (moss_large_gap_occupation_sum_bound hk hν hπ hkn)
          (24 * Real.sqrt ((k : ℝ) * n)))
