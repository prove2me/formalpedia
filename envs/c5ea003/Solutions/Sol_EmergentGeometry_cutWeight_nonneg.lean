-- Prove2me | solution 1 for EmergentGeometry.cutWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:30:57.814998+00:00
-- url     : https://prove2.me/submissions/4191dc31-7dd0-469c-821e-3129d4945ff3

import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

open EmergentGeometry Finset

variable {V : Type*} [Fintype V]

theorem solution (G : BulkGraph V) (f : Region V) : 0 ≤ cutWeight G f := by
  simp only [cutWeight]
  refine div_nonneg ?_ (by norm_num)
  refine sum_nonneg fun u _ => sum_nonneg fun v _ => ?_
  exact mul_nonneg (Nat.cast_nonneg _) (G.weight_nonneg u v)
