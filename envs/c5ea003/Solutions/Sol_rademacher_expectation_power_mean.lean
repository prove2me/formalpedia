-- Prove2me | solution 1 for rademacher_expectation_power_mean
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T21:38:03.823961+00:00
-- url     : https://prove2.me/submissions/3412cf4a-7df6-4a1b-8fc8-fb260c6937d1

import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.MeanInequalitiesPow
open MatrixCompletion
open scoped BigOperators

theorem solution
    {n1 n2 : Nat} (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s)
    (F : Finset (Fin n1 × Fin n2) → ℝ) (hF : ∀ eps, 0 ≤ F eps) :
    rademacherExpectation (fun eps => (F eps) ^ r)
      ≤ Real.rpow (rademacherExpectation (fun eps => (F eps) ^ s)) (r / s) := by
  classical
  set N : ℕ := Fintype.card (Fin n1 × Fin n2) with hN
  set w : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => rademacherObservationWeight eps with hw
  have hwnn : ∀ eps : Finset (Fin n1 × Fin n2), 0 ≤ w eps := by
    intro eps
    simp only [hw, rademacherObservationWeight]
    positivity
  have hwsum : ∑ eps : Finset (Fin n1 × Fin n2), w eps = 1 := by
    simp only [hw, rademacherObservationWeight]
    rw [Finset.sum_const]
    have hcard : (Finset.univ : Finset (Finset (Fin n1 × Fin n2))).card
        = 2 ^ N := by
      rw [Finset.card_univ, hN]
      exact Fintype.card_finset
    rw [hcard]
    rw [nsmul_eq_mul]
    rw [← hN]
    rw [div_pow, one_pow]
    rw [mul_one_div]
    rw [div_eq_one_iff_eq]
    · push_cast; ring
    · positivity
  have hp : (1 : ℝ) ≤ s / r := by
    rw [le_div_iff₀ hr]; linarith
  have hznn : ∀ eps : Finset (Fin n1 × Fin n2), 0 ≤ (F eps) ^ r := by
    intro eps
    exact Real.rpow_nonneg (hF eps) r
  have key := Real.arith_mean_le_rpow_mean (Finset.univ)
    w (fun eps => (F eps) ^ r)
    (fun i _ => hwnn i) hwsum (fun i _ => hznn i) hp
  have hpow : ∀ eps : Finset (Fin n1 × Fin n2),
      ((F eps) ^ r) ^ (s / r) = (F eps) ^ s := by
    intro eps
    rw [← Real.rpow_mul (hF eps)]
    congr 1
    field_simp
  have hexp : (1 : ℝ) / (s / r) = r / s := by
    rw [one_div_div]
  simp only [rademacherExpectation]
  calc ∑ eps : Finset (Fin n1 × Fin n2),
        rademacherObservationWeight eps * (F eps) ^ r
      = ∑ eps : Finset (Fin n1 × Fin n2), w eps * (F eps) ^ r := by rfl
    _ ≤ (∑ eps : Finset (Fin n1 × Fin n2), w eps * ((F eps) ^ r) ^ (s / r)) ^ (1 / (s / r)) := key
    _ = (∑ eps : Finset (Fin n1 × Fin n2), w eps * (F eps) ^ s) ^ (r / s) := by
          rw [hexp]
          congr 1
          apply Finset.sum_congr rfl
          intro eps _
          rw [hpow eps]
    _ = Real.rpow (∑ eps : Finset (Fin n1 × Fin n2),
          rademacherObservationWeight eps * (F eps) ^ s) (r / s) := by rfl
