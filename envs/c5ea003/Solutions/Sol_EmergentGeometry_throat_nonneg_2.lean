-- Prove2me | solution 2 for EmergentGeometry.throat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:51:24.490039+00:00
-- url     : https://prove2.me/submissions/9873e536-0c6c-4305-b71f-2c5908c6d825

import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : BulkGraph V) (A B : Region V) :
    0 ≤ throat G A B := by
  have hcw : ∀ f : Region V, 0 ≤ cutWeight G f := by
    intro f
    simp only [cutWeight]
    apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 2)
    refine Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => ?_))
    exact mul_nonneg (by positivity) (G.weight_nonneg u v)
  unfold throat
  by_cases h : (sepSet A B).Nonempty
  · rw [dif_pos h]
    exact Finset.le_inf' _ _ (fun f _ => hcw f)
  · rw [dif_neg h]
