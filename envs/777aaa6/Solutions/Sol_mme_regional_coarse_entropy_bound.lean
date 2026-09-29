-- Prove2me | solution 1 for mme_regional_coarse_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:18:46.138508+00:00
-- url     : https://prove2.me/submissions/11c79f10-6aa1-411f-bf3a-3e36dc7a93d1

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_regional_entropy_coarsening
import Mathlib
open BigOperators MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) :
    coarsePotential m i ≤ jointPotential m := by
  unfold coarsePotential jointPotential
  apply Finset.sum_le_sum
  intro r _
  have h := mme_regional_entropy_coarsening (fun c : MME.RecursiveThinSplit.Split half (parent r) ↦ c.val i)
    (fun c ↦ (m r c : ℝ)) (fun c ↦ Nat.cast_nonneg _)
  simp only [marginalCounts,Nat.cast_sum]
  convert h using 1
  congr 1
  funext j
  apply Finset.sum_congr
  · ext c; simp only [Finset.mem_univ]
  · intro c _; rfl
