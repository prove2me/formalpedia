-- Prove2me | solution 2 for fixed_cardinality_event_failure_probability_antitone_of_event_mono
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T03:22:32.843939+00:00
-- url     : https://prove2.me/submissions/ebfe5828-7cb4-4d01-a89e-ae46152b4548

import Theorems.Thm_fixed_cardinality_event_probability_monotone_of_event_mono
import Definitions.Def_matrix_completion_fixed_cardinality

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    (∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' → Event Omega → Event Omega') →
    ∀ k m : ℕ, k ≤ m → m ≤ n₁ * n₂ →
      1 - fixedCardinalityEventProb m Event ≤
        1 - fixedCardinalityEventProb k Event := by
  intro hmono k m hkm hmle
  have h := fixed_cardinality_event_probability_monotone_of_event_mono
    Event hmono k m hkm hmle
  linarith
