-- Prove2me | solution 1 for HilbertCompression.quadratic_identity_reduces
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:30:50.281393+00:00
-- url     : https://prove2.me/submissions/618efa65-e481-46f5-ae4f-3a40b5e487a2

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open ContinuousLinearMap

private theorem soma_quadrados_operadores_nula
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (h : star A * A + star B * B = 0) :
    A = 0 ∧ B = 0 := by
  have hnorma (v : H) : ‖A v‖ ^ 2 + ‖B v‖ ^ 2 = 0 := by
    have hAv : (inner ℂ (A v) (A v)).re = ‖A v‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (A v)
    have hBv : (inner ℂ (B v) (B v)).re = ‖B v‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (B v)
    have hvetor := congrArg (fun T : H →L[ℂ] H => (inner ℂ v (T v)).re) h
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.zero_apply, inner_add_right, inner_zero_right, Complex.add_re,
      Complex.zero_re, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hAv, hBv] using hvetor
  have hA (v : H) : A v = 0 := by
    apply norm_eq_zero.mp
    nlinarith [hnorma v, sq_nonneg ‖B v‖, norm_nonneg (A v)]
  have hB (v : H) : B v = 0 := by
    apply norm_eq_zero.mp
    nlinarith [hnorma v, sq_nonneg ‖A v‖, norm_nonneg (B v)]
  exact ⟨ContinuousLinearMap.ext hA, ContinuousLinearMap.ext hB⟩

private theorem comuta_de_bloco_nulo
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X P : H →L[ℂ] H) (hX : star X = X) (hP : star P = P)
    (hbloco : (1 - P) * X * P = 0) : P * X = X * P := by
  have hx : X * P = P * X * P := by
    have := hbloco
    simpa only [sub_mul, one_mul, sub_eq_zero] using this
  have hpx : P * X = P * X * P := by
    have hestrela := congrArg star hx
    simpa only [star_mul, hX, hP, mul_assoc] using hestrela
  exact hpx.trans hx.symm

/-- A igualdade da soma de quadrados comprimida força a projeção a reduzir os dois
operadores autoadjuntos, sem restrição de dimensão, positividade ou comutatividade. -/
theorem solution
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X Y P : H →L[ℂ] H)
    (hX : star X = X) (hY : star Y = Y)
    (hP : star P = P) (hPP : P * P = P)
    (hquadrado : P * (X * X + Y * Y) * P =
      (P * X * P) * (P * X * P) + (P * Y * P) * (P * Y * P)) :
    P * X = X * P ∧ P * Y = Y * P := by
  have hPPdireita (Z : H →L[ℂ] H) : P * (P * Z) = P * Z := by
    rw [← mul_assoc, hPP]
  have hidentidade (Z : H →L[ℂ] H) (hZ : star Z = Z) :
      star ((1 - P) * Z * P) * ((1 - P) * Z * P) =
        P * (Z * Z) * P - (P * Z * P) * (P * Z * P) := by
    simp only [star_mul, star_sub, star_one, hP, hZ]
    noncomm_ring [hPPdireita]
  have hsoma : star ((1 - P) * X * P) * ((1 - P) * X * P) +
      star ((1 - P) * Y * P) * ((1 - P) * Y * P) = 0 := by
    rw [hidentidade X hX, hidentidade Y hY]
    calc
      _ = P * (X * X + Y * Y) * P -
          ((P * X * P) * (P * X * P) + (P * Y * P) * (P * Y * P)) := by
        noncomm_ring
      _ = 0 := sub_eq_zero.mpr hquadrado
  obtain ⟨hx, hy⟩ := soma_quadrados_operadores_nula _ _ hsoma
  exact ⟨comuta_de_bloco_nulo X P hX hP hx, comuta_de_bloco_nulo Y P hY hP hy⟩
