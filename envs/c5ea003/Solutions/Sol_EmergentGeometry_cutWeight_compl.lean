-- Prove2me | solution 1 for EmergentGeometry.cutWeight_compl
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:28:19.318317+00:00
-- url     : https://prove2.me/submissions/af061f42-4b94-4454-aa88-ed67558adcfb

import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

open EmergentGeometry Finset

variable {V : Type*} [Fintype V]

theorem solution (G : BulkGraph V) (f : Region V) :
    cutWeight G (fun v => !(f v)) = cutWeight G f := by
  unfold cutWeight
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  -- sepBit (!a) (!b) = sepBit a b
  have h : (sepBit (!(f u)) (!(f v)) : ℝ) = (sepBit (f u) (f v) : ℝ) := by
    simp [sepBit, Bool.not_eq_not]
  rw [h]
