-- Prove2me | solution 1 for bottleneck_set_is_optimal_for_one_step_throughput
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:48:12.849978+00:00
-- url     : https://prove2.me/submissions/1e25bc2e-a211-4545-87f2-efbbe3c123ae

import Mathlib
import Definitions.Def_Bridges_BottleneckUpgrade
open Finset in
theorem solution {α : Type*} [DecidableEq α]
    (s u : Finset α) (c : α → ℕ) (hs : s.Nonempty)
    (_hu : u ⊆ s)
    (hcard : u.card = (bottleneckSet s c hs).card) :
    s.inf' hs (unitUpgradeOn u c) ≤
      s.inf' hs (unitUpgradeOn (bottleneckSet s c hs) c) := by
  set m := s.inf' hs c with hm
  obtain ⟨x, hx, hxm⟩ := exists_mem_eq_inf' hs c
  -- any upgrade leaves a minimiser at `≤ m + 1`
  have hLHS : s.inf' hs (unitUpgradeOn u c) ≤ m + 1 := by
    refine (inf'_le _ hx).trans ?_
    unfold unitUpgradeOn
    split_ifs <;> omega
  -- upgrading the whole bottleneck lifts every capacity to `≥ m + 1`
  have hRHS : m + 1 ≤ s.inf' hs (unitUpgradeOn (bottleneckSet s c hs) c) := by
    refine le_inf' _ _ fun y hy => ?_
    unfold unitUpgradeOn
    by_cases hyB : y ∈ bottleneckSet s c hs
    · rw [if_pos hyB]
      have := (mem_filter.mp hyB).2
      omega
    · rw [if_neg hyB]
      have hle : m ≤ c y := inf'_le c hy
      have hne : c y ≠ m := fun h => hyB (mem_filter.mpr ⟨hy, h⟩)
      omega
  exact hLHS.trans hRHS
