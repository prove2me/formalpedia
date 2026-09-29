-- Prove2me | solution 1 for bernoulli_event_complement_probability
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T23:03:24.076543+00:00
-- url     : https://prove2.me/submissions/37c0e820-b605-44d4-aae5-fe3e122dbc42

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion
open scoped BigOperators

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ) (E : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p E + bernoulliEventProb p (fun Ω => ¬ E Ω) = 1 := by
  classical
  unfold bernoulliEventProb
  simp only []
  rw [← Finset.sum_add_distrib]
  trans (∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω)
  · refine Finset.sum_congr rfl (fun Ω _ => ?_)
    by_cases h : E Ω <;> simp [h]
  unfold bernoulliObservationWeight
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p)
    (fun _ : Fin n₁ × Fin n₂ => (1 - p))
  have hone : (∏ _a : Fin n₁ × Fin n₂, (p + (1 - p))) = 1 := by simp
  rw [hone] at hpa
  have hrw : ∀ t : Finset (Fin n₁ × Fin n₂),
      (∏ _a ∈ t, p) * ∏ _a ∈ tᶜ, (1 - p) =
        p ^ t.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - t.card) := by
    intro t
    rw [Finset.prod_const, Finset.prod_const, Finset.card_compl]
  rw [Finset.sum_congr rfl (fun t _ => hrw t)] at hpa
  exact hpa.symm
