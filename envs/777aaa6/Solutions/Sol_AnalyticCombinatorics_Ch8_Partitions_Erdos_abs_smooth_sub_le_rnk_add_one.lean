-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.abs_smooth_sub_le_rnk_add_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:10:31.683059+00:00
-- url     : https://prove2.me/submissions/552533fd-e5c4-4bed-9b77-c7537e8611f3

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: smooth scale vs floored rank

The floored rank `rnk n = ⌊3√n⌋` is NOT an approximate martingale (the fractional part `frac(3√n)`
contributes an `Θ(1)` phase obstruction).  The smooth scale `3√n` IS, so the occupation/Tanaka argument
runs on the smooth difference `3√x − 3√y`; the window is transferred back to the `rnk`-window with a
constant `+1` slack, since `|3√x − 3√y| ≤ |rnk x − rnk y| + 1`.  Opus-authored.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos in
theorem solution (x y : ℕ) :
    |3 * Real.sqrt x - 3 * Real.sqrt y|
      ≤ ((Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ))) : ℝ) + 1 := by
  have hax1 : (rnk x : ℝ) ≤ 3 * Real.sqrt x := by
    rw [rnk]; exact_mod_cast Nat.floor_le (by positivity)
  have hax2 : 3 * Real.sqrt x < (rnk x : ℝ) + 1 := by
    rw [rnk]; exact_mod_cast Nat.lt_floor_add_one (3 * Real.sqrt x)
  have hay1 : (rnk y : ℝ) ≤ 3 * Real.sqrt y := by
    rw [rnk]; exact_mod_cast Nat.floor_le (by positivity)
  have hay2 : 3 * Real.sqrt y < (rnk y : ℝ) + 1 := by
    rw [rnk]; exact_mod_cast Nat.lt_floor_add_one (3 * Real.sqrt y)
  have hnat : ((Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ))) : ℝ)
      = |(rnk x : ℝ) - (rnk y : ℝ)| := by
    rw [Int.cast_natAbs]; push_cast; rfl
  rw [hnat, abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [hay2, hax1, neg_abs_le ((rnk x : ℝ) - (rnk y : ℝ))]
  · nlinarith [hax2, hay1, le_abs_self ((rnk x : ℝ) - (rnk y : ℝ))]
