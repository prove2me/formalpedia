-- Prove2me | solution 1 for lean_workbook_plus_17889
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:02:56.555778+00:00
-- url     : https://prove2.me/submissions/0585aa5a-b8a2-45e0-86d3-6a91fff5d8a5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open scoped ComplexOrder

theorem self_commutator_energy_identity {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) :
    let C := A * A.conjTranspose - A.conjTranspose * A
    (C.conjTranspose * C).trace =
      (A.conjTranspose * (C * A - A * C)).trace := by
  dsimp only
  let C := A * A.conjTranspose - A.conjTranspose * A
  change (C.conjTranspose * C).trace =
    (A.conjTranspose * (C * A - A * C)).trace
  have hstar : C.conjTranspose = C := by
    simp [C, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hcyc : (A * A.conjTranspose * C).trace =
      (A.conjTranspose * (C * A)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm A, Matrix.mul_assoc]
  rw [hstar]
  calc
    (C * C).trace =
        (A * A.conjTranspose * C).trace - (A.conjTranspose * A * C).trace := by
      change ((A * A.conjTranspose - A.conjTranspose * A) * C).trace = _
      rw [sub_mul, Matrix.trace_sub]
    _ = (A.conjTranspose * (C * A - A * C)).trace := by
      conv_rhs => rw [mul_sub, Matrix.trace_sub]
      rw [hcyc, Matrix.mul_assoc]

theorem normal_of_commute_self_commutator {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ)
    (h : Commute A (A * A.conjTranspose - A.conjTranspose * A)) :
    A * A.conjTranspose = A.conjTranspose * A := by
  have he := self_commutator_energy_identity A
  dsimp only at he
  rw [← h.eq, sub_self, mul_zero, Matrix.trace_zero] at he
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp he)

theorem normal_iff_commute_self_commutator {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) :
    Commute A (A * A.conjTranspose - A.conjTranspose * A) ↔
      Commute A A.conjTranspose := by
  constructor
  · exact normal_of_commute_self_commutator A
  · intro h
    rw [h.eq, sub_self]
    exact Commute.zero_right A

theorem self_commutator_nilpotent_of_commute {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (A : Matrix ι ι ℂ)
    (h : Commute A (A * A.conjTranspose - A.conjTranspose * A)) :
    IsNilpotent (A * A.conjTranspose - A.conjTranspose * A) := by
  rw [normal_of_commute_self_commutator A h, sub_self]
  exact ⟨1, by simp⟩

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : A * A.conjTranspose - A.conjTranspose * A = 0) :
    A * A.conjTranspose = A.conjTranspose * A :=
  sub_eq_zero.mp h

#print axioms solution
#print axioms self_commutator_energy_identity
#print axioms normal_of_commute_self_commutator
#print axioms normal_iff_commute_self_commutator
#print axioms self_commutator_nilpotent_of_commute
