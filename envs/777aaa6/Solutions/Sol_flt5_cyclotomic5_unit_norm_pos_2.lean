-- Prove2me | solution 2 for flt5_cyclotomic5_unit_norm_pos
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T13:55:17.073033+00:00
-- url     : https://prove2.me/submissions/4605b53d-fe06-4c8a-8885-ea159d629db5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic
import Theorems.Thm_flt5_ck5_norm_nonneg

-- Sketch: 0 < Algebra.norm ℤ (u : ZZ5) for unit u : ZZ5ˣ
-- Strategy:
-- 1. N_ℤ(u) is a unit in ℤ (monoid hom preserves units), so N_ℤ(u) ∈ {1,-1}
-- 2. If N_ℤ(u) = -1: cast to ℚ gives N_ℚ(u:CK5) = -1 (via Algebra.coe_norm_int)
-- 3. Child flt5_ck5_norm_nonneg: N_ℚ(u:CK5) ≥ 0 (CK5 totally imaginary)
-- 4. Contradiction: -1 ≥ 0 is false. So N_ℤ(u) = 1 > 0.

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
  -- Step 1: N(u) is a unit in ℤ, hence ±1
  have hnu : IsUnit (Algebra.norm ℤ (u : ZZ5unp)) :=
    IsUnit.map (Algebra.norm ℤ) (Units.isUnit u)
  rw [Int.isUnit_iff] at hnu
  rcases hnu with h | h
  · linarith [h ▸ (show (0 : ℤ) < 1 by norm_num)]
  · -- N(u) = -1: contradiction with totally imaginary norm ≥ 0
    exfalso
    -- Child: N_ℚ((u:ZZ5unp):CK5unp) ≥ 0
    have hnneg : (0 : ℚ) ≤ Algebra.norm ℚ ((u : ZZ5unp) : CK5unp) :=
      flt5_ck5_norm_nonneg ((u : ZZ5unp) : CK5unp)
    -- Cast: (N_ℤ u : ℚ) = N_ℚ(u:CK5)
    have hcast : (Algebra.norm ℤ (u : ZZ5unp) : ℚ) = Algebra.norm ℚ ((u : ZZ5unp) : CK5unp) := by
      rw [Algebra.coe_norm_int]
    rw [h] at hcast
    norm_num at hcast
    linarith [hcast ▸ hnneg]

end
