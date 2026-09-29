-- Prove2me | solution 1 for bernoulli_powerset_expectation_prod_factor
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T20:52:05.96333+00:00
-- url     : https://prove2.me/submissions/7db64eff-cafc-44d2-80c0-9d9eebc757b5

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

/-- `bernoulli_powerset_expectation_prod_factor`.

**Independence / product factorization of the Bernoulli powerset expectation.**
For any per-coordinate function `f : (Fin n₁ × Fin n₂) → ℝ → ℝ`, the expectation
of the product `∏_w f w (𝟙[w ∈ Ω])` over the Bernoulli powerset measure with
inclusion probability `p` factorizes into a product of per-coordinate
expectations `p·f w 1 + (1-p)·f w 0`. This is the precise statement that the
coordinate inclusion indicators `𝟙[w ∈ Ω]` are independent under the powerset
measure, proved directly by the binomial expansion `Finset.prod_add`
(`∏_w (a_w + b_w) = ∑_{Ω⊆univ} (∏_{w∈Ω} a_w)(∏_{w∉Ω} b_w)`). -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ)
    (f : (Fin n₁ × Fin n₂) → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∏ w : Fin n₁ × Fin n₂, f w (if w ∈ Omega then 1 else 0)) =
      ∏ w : Fin n₁ × Fin n₂, (p * f w 1 + (1 - p) * f w 0) := by
  classical
  have hpa := Finset.prod_add (fun w : Fin n₁ × Fin n₂ => p * f w 1)
    (fun w => (1 - p) * f w 0) Finset.univ
  rw [hpa, Finset.powerset_univ]
  unfold bernoulliExpectation bernoulliObservationWeight
  apply Finset.sum_congr rfl
  intro t _
  simp only []
  have hsplit :
      (∏ w : Fin n₁ × Fin n₂, f w (if w ∈ t then 1 else 0)) =
        (∏ w ∈ t, f w 1) * ∏ w ∈ Finset.univ \ t, f w 0 := by
    rw [← Finset.prod_mul_prod_compl t (fun w => f w (if w ∈ t then 1 else 0)),
        Finset.compl_eq_univ_sdiff]
    congr 1
    · apply Finset.prod_congr rfl; intro w hw; simp [hw]
    · apply Finset.prod_congr rfl; intro w hw
      simp only [Finset.mem_sdiff] at hw; simp [hw.2]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, hsplit]
  rw [Finset.card_univ_diff]; ring
