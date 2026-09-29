-- Prove2me | solution 1 for centered_sampling_chernoff_exponential_tail
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T00:07:09.163456+00:00
-- url     : https://prove2.me/submissions/87ba12e0-2aec-4d9e-b0b7-da49ab460bc6

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Exp
open MatrixCompletion
open scoped BigOperators Classical
set_option maxHeartbeats 800000

namespace ChernoffBank
variable {n₁ n₂ : ℕ}

theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

end ChernoffBank

open ChernoffBank in
/-- `centered_sampling_chernoff_exponential_tail`.
Cramér–Chernoff exponential tail bound on the bespoke Bernoulli measure:
`P(t ≤ Z) ≤ exp(-λ t) · E[exp(λ·Z)]` for `0 ≤ p ≤ 1`, `λ > 0`. -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (t lam : ℝ) (hlam : 0 < lam) :
    bernoulliEventProb p (fun Omega => t ≤ Z Omega) ≤
      Real.exp (-(lam * t)) *
        bernoulliExpectation p (fun Omega => Real.exp (lam * Z Omega)) := by
  classical
  unfold bernoulliEventProb bernoulliExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Omega _
  have hw : 0 ≤ bernoulliObservationWeight p Omega := weight_nonneg p hp0 hp1 Omega
  by_cases h : t ≤ Z Omega
  · simp only [h, if_true]
    have hexp : (1:ℝ) ≤ Real.exp (lam * (Z Omega - t)) := by
      rw [Real.one_le_exp_iff]
      have : 0 ≤ Z Omega - t := by linarith
      positivity
    calc bernoulliObservationWeight p Omega
        = bernoulliObservationWeight p Omega * 1 := by ring
      _ ≤ bernoulliObservationWeight p Omega * Real.exp (lam * (Z Omega - t)) :=
            mul_le_mul_of_nonneg_left hexp hw
      _ = Real.exp (-(lam * t)) *
            (bernoulliObservationWeight p Omega * Real.exp (lam * Z Omega)) := by
            have hcancel : Real.exp (-(lam * t)) * Real.exp (lam * Z Omega)
                = Real.exp (lam * (Z Omega - t)) := by
              rw [← Real.exp_add]; ring_nf
            rw [show Real.exp (-(lam * t)) *
                  (bernoulliObservationWeight p Omega * Real.exp (lam * Z Omega))
                  = bernoulliObservationWeight p Omega *
                    (Real.exp (-(lam * t)) * Real.exp (lam * Z Omega)) by ring,
               hcancel]
  · simp only [h, if_false]
    have : 0 ≤ Real.exp (-(lam * t)) *
        (bernoulliObservationWeight p Omega * Real.exp (lam * Z Omega)) := by
      positivity
    exact this
