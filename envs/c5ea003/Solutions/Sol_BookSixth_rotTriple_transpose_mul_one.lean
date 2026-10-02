-- Prove2me | solution 1 for BookSixth.rotTriple_transpose_mul_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T01:13:38.883366+00:00
-- url     : https://prove2.me/submissions/cdb2e372-f943-4c89-a23b-900ac2e2bdf6

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
open scoped BigOperators
open scoped Matrix
open BookSixth Matrix

noncomputable section

lemma rot01_transpose_mul (θ : ℝ) : (rot01Matrix θ)ᵀ * rot01Matrix θ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot01Matrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    ring_nf <;> nlinarith [Real.cos_sq_add_sin_sq θ]
lemma rot02_transpose_mul (θ : ℝ) : (rot02Matrix θ)ᵀ * rot02Matrix θ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot02Matrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    ring_nf <;> nlinarith [Real.cos_sq_add_sin_sq θ]
lemma rot12_transpose_mul (θ : ℝ) : (rot12Matrix θ)ᵀ * rot12Matrix θ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot12Matrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    ring_nf <;> nlinarith [Real.cos_sq_add_sin_sq θ]

lemma trans_mul_trans {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) : (A * B)ᵀ * (A * B) = 1 := by
  rw [transpose_mul]
  calc Bᵀ * Aᵀ * (A * B) = Bᵀ * ((Aᵀ * A) * B) := by
        simp only [Matrix.mul_assoc]
    _ = Bᵀ * (1 * B) := by rw [hA]
    _ = Bᵀ * B := by rw [Matrix.one_mul]
    _ = 1 := hB

lemma trans_mul_trans3 {A B C : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) (hC : Cᵀ * C = 1) :
    (A * B * C)ᵀ * (A * B * C) = 1 := by
  have hAB : (A * B)ᵀ * (A * B) = 1 := trans_mul_trans hA hB
  rw [show A * B * C = (A * B) * C by simp only [Matrix.mul_assoc],
    transpose_mul]
  calc Cᵀ * (A * B)ᵀ * ((A * B) * C) = Cᵀ * ((A * B)ᵀ * (A * B)) * C := by
        simp only [Matrix.mul_assoc]
    _ = Cᵀ * C := by rw [hAB, Matrix.mul_one]
    _ = 1 := hC

-- the composite
lemma rotM_transpose_mul (t θ1 θ2 θ3 : ℝ) :
    (rot12Matrix (t * θ3) * rot02Matrix (t * θ2) * rot01Matrix (t * θ1))ᵀ *
      (rot12Matrix (t * θ3) * rot02Matrix (t * θ2) * rot01Matrix (t * θ1)) = 1 := by
  have hAB : (rot12Matrix (t * θ3) * rot02Matrix (t * θ2))ᵀ *
      (rot12Matrix (t * θ3) * rot02Matrix (t * θ2)) = 1 :=
    trans_mul_trans (rot12_transpose_mul _) (rot02_transpose_mul _)
  exact trans_mul_trans hAB (rot01_transpose_mul _)

open BookSixth

-- The threefold coordinate rotation is orthogonal: the transpose of the
--composite is its inverse.  This is the algebraic heart of the isotopy; it is
--what lets the inverse leg of `H` be written as a transpose.

theorem solution (θ1 θ2 θ3 : ℝ) :
    (rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1)ᵀ
      * (rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1) = 1 := by
  have h := rotM_transpose_mul 1 θ1 θ2 θ3
  simpa only [one_mul] using h
