-- Prove2me | solution 1 for bernoulli_expectation_sqrt_le_sqrt_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T14:29:32.868146+00:00
-- url     : https://prove2.me/submissions/d3673f08-82e0-4c2d-a3c2-5e217c49fc50

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ p → p ≤ 1 → (∀ Ω, 0 ≤ F Ω) →
    bernoulliExpectation p (fun Ω => Real.sqrt (F Ω)) ≤
      Real.sqrt (bernoulliExpectation p F) := by
  intro hp0 hp1 hF
  classical
  -- weight nonnegativity
  have hw : ∀ Ω : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Ω := by
    intro Ω
    unfold bernoulliObservationWeight
    have h1p : (0:ℝ) ≤ 1 - p := by linarith
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg h1p _)
  -- weights sum to one
  have hsum1 : ∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω = 1 := by
    unfold bernoulliObservationWeight
    rw [Fintype.sum_pow_mul_eq_add_pow (Fin n₁ × Fin n₂) p (1 - p)]
    simp
  -- E_p[F] ≥ 0
  have hEFnonneg : 0 ≤ bernoulliExpectation p F := by
    unfold bernoulliExpectation
    apply Finset.sum_nonneg
    intro Ω _
    exact mul_nonneg (hw Ω) (hF Ω)
  -- Cauchy–Schwarz: (∑ w·√F)² ≤ (∑ w)·(∑ w·F)
  have hCS :
      (∑ Ω : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Ω * Real.sqrt (F Ω)) ^ 2 ≤
        (∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω) *
          (∑ Ω : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Ω * F Ω) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun Ω _ => hw Ω)
      (fun Ω _ => mul_nonneg (hw Ω) (hF Ω))
      (fun Ω _ => ?_)
    -- (w·√F)² = w · (w·F)
    rw [mul_pow, Real.sq_sqrt (hF Ω)]
    ring
  -- assemble
  have hLHSnonneg : 0 ≤ bernoulliExpectation p (fun Ω => Real.sqrt (F Ω)) := by
    unfold bernoulliExpectation
    apply Finset.sum_nonneg
    intro Ω _
    exact mul_nonneg (hw Ω) (Real.sqrt_nonneg _)
  rw [Real.le_sqrt hLHSnonneg hEFnonneg]
  -- goal: (E √F)² ≤ E F
  have := hCS
  rw [hsum1, one_mul] at this
  simpa [bernoulliExpectation] using this
