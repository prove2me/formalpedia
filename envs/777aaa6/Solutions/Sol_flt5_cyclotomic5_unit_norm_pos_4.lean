-- Prove2me | solution 4 for flt5_cyclotomic5_unit_norm_pos
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:49:45.384392+00:00
-- url     : https://prove2.me/submissions/7992b49e-d98c-4b70-abcd-5cdb32913999
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_flt5_ck5_norm_nonneg

-- Sketch: 0 < Algebra.norm ℤ (u : ZZ5) for unit u : ZZ5ˣ
-- Strategy:
-- 1. N_ℤ(u) is a unit in ℤ (monoid hom preserves units), so N_ℤ(u) ∈ {1,-1}
-- 2. If N_ℤ(u) = 1: done, 0 < 1.
-- 3. If N_ℤ(u) = -1: contradiction via N_ℚ ≥ 0 (CK5 totally imaginary).

noncomputable section

abbrev ZZ5unp := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5unp := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5unp :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5unp :=
  IsCyclotomicExtension.numberField {5} ℚ CK5unp

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (u : ZZ5unpˣ) :
    0 < Algebra.norm ℤ (u : ZZ5unp) := by
  have hnu : IsUnit (Algebra.norm ℤ (u : ZZ5unp)) :=
    IsUnit.map (Algebra.norm ℤ) (Units.isUnit u)
  rw [Int.isUnit_iff] at hnu
  rcases hnu with h | h
  · -- N(u) = 1 > 0
    omega
  · -- N(u) = -1: contradiction with N_ℚ ≥ 0
    exfalso
    have hnneg : (0 : ℚ) ≤ Algebra.norm ℚ ((u : ZZ5unp) : CK5unp) :=
      flt5_ck5_norm_nonneg ((u : ZZ5unp) : CK5unp)
    have hcast : (Algebra.norm ℤ (u : ZZ5unp) : ℚ) = Algebra.norm ℚ ((u : ZZ5unp) : CK5unp) :=
      Algebra.coe_norm_int (u : ZZ5unp)
    rw [h] at hcast
    push_cast at hcast
    linarith

end
