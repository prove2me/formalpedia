-- Prove2me | solution 1 for bernoulli_powerset_expectation_double
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T21:08:12.761266+00:00
-- url     : https://prove2.me/submissions/1ec82170-5222-4fcb-ad2e-e7d22f8c3612

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

/-- `bernoulli_powerset_expectation_double`.

**Double linearity** of the Bernoulli powerset expectation: the expectation of a
double coordinate sum of functions of two inclusion indicators pushes through both
sums term-by-term. Proved by distributing the weight into the inner double sum and
swapping the order of summation twice (`Finset.sum_comm`), so that the
expectation `∑_Ω` lands innermost. This is the form used to expand the second
moment (variance) of a statistic linear in the inclusion indicators into a
double sum of pair-coordinate expectations. -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ)
    (G : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → ℝ → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∑ w : Fin n₁ × Fin n₂, ∑ w' : Fin n₁ × Fin n₂,
          G w w' (if w ∈ Omega then 1 else 0) (if w' ∈ Omega then 1 else 0)) =
      ∑ w : Fin n₁ × Fin n₂, ∑ w' : Fin n₁ × Fin n₂,
        bernoulliExpectation p
          (fun Omega => G w w' (if w ∈ Omega then 1 else 0) (if w' ∈ Omega then 1 else 0)) := by
  classical
  unfold bernoulliExpectation
  have hdist : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega *
        (∑ w : Fin n₁ × Fin n₂, ∑ w' : Fin n₁ × Fin n₂,
          G w w' (if w ∈ Omega then 1 else 0) (if w' ∈ Omega then 1 else 0)) =
      ∑ w : Fin n₁ × Fin n₂, ∑ w' : Fin n₁ × Fin n₂,
        bernoulliObservationWeight p Omega *
          G w w' (if w ∈ Omega then 1 else 0) (if w' ∈ Omega then 1 else 0) := by
    intro Omega; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro w _; rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun Omega _ => hdist Omega), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _; rw [Finset.sum_comm]
