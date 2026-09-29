-- Prove2me | solution 3 for flt5_zz5_unit_norm_one
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:42:38.046084+00:00
-- url     : https://prove2.me/submissions/1f1fdd49-55d5-4edf-acfa-666985c667b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic
import Theorems.Thm_flt5_zz5_unit_norm_one
import Theorems.Thm_flt5_cyclotomic5_unit_norm_pos

-- Sketch: flt5_zz5_unit_norm_one
-- Strategy:
--   1. N(u) is a unit in ℤ (from IsUnit + monoid hom)
--   2. Int.isUnit_iff: N(u) = 1 ∨ N(u) = -1
--   3. Child flt5_cyclotomic5_unit_norm_pos: 0 < N(u) for units u in ZZ5
--   4. Combine: N(u) = 1

noncomputable section

abbrev ZZ5un := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)

instance : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField (CyclotomicField 5 ℚ) :=
  IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)

theorem solution (u : ZZ5unˣ) :
    Algebra.norm ℤ (u : ZZ5un) = 1 := by
  -- Step 1: N(u) is a unit in ℤ since N is a monoid hom and u is a unit
  have hnu : IsUnit (Algebra.norm ℤ (u : ZZ5un)) :=
    IsUnit.map (Algebra.norm ℤ) (Units.isUnit u)
  -- Step 2: units of ℤ are ±1
  rw [Int.isUnit_iff] at hnu
  rcases hnu with h | h
  · exact h
  · -- N(u) = -1: contradiction with positivity
    exfalso
    have hpos : 0 < Algebra.norm ℤ (u : ZZ5un) := flt5_cyclotomic5_unit_norm_pos u
    linarith [h.symm ▸ hpos]

end
