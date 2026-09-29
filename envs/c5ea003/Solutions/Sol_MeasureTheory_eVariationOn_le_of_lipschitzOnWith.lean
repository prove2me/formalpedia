-- Prove2me | solution 1 for MeasureTheory.eVariationOn_le_of_lipschitzOnWith
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:20:24.210272+00:00
-- url     : https://prove2.me/submissions/59394f9f-44e0-4afa-83e1-9c218bf47a56

import Mathlib

open Set

universe u

theorem solution {F : Type u} [PseudoEMetricSpace F] (f : ℝ → F) (C : NNReal) (a b : ℝ)
    (hab : a ≤ b) (hf : LipschitzOnWith C f (Set.Icc a b)) :
    eVariationOn f (Set.Icc a b) ≤ ENNReal.ofReal (C * (b - a)) := by
  have hid : eVariationOn (id : ℝ → ℝ) (Set.Icc a b) ≤ ENNReal.ofReal (b - a) := by
    have hmono : MonotoneOn (id : ℝ → ℝ) (Set.Icc a b) := fun x _ y _ hxy => hxy
    have h := hmono.eVariationOn_le (a := a) (b := b) (by simp [hab]) (by simp [hab])
    simpa using h
  have hcomp : eVariationOn (f ∘ id) (Set.Icc a b)
      ≤ (C : ENNReal) * eVariationOn (id : ℝ → ℝ) (Set.Icc a b) :=
    hf.comp_eVariationOn_le (Set.mapsTo_id _)
  have hfin : eVariationOn f (Set.Icc a b)
      ≤ (C : ENNReal) * ENNReal.ofReal (b - a) := by
    refine le_trans hcomp ?_
    exact mul_le_mul_left' hid _
  refine le_trans hfin (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
