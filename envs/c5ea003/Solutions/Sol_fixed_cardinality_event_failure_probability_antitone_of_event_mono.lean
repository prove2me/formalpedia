-- Prove2me | solution 1 for fixed_cardinality_event_failure_probability_antitone_of_event_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-13T23:55:42.101237+00:00
-- url     : https://prove2.me/submissions/902f838e-2cbb-466a-adf5-f0cf0bf783e6

import Mathlib.Tactic
import Theorems.Thm_fixed_cardinality_event_failure_probability_antitone_of_event_mono
import Theorems.Thm_fixed_cardinality_event_probability_monotone_of_event_mono

open MatrixCompletion

/-- Convert monotonicity of fixed-cardinality success probability into
antitonicity of fixed-cardinality failure probability. -/
theorem solution
    {n₁ n₂ : ℕ} (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    (∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' → Event Omega → Event Omega') →
    ∀ k m : ℕ, k ≤ m → m ≤ n₁ * n₂ →
      1 - fixedCardinalityEventProb m Event ≤
        1 - fixedCardinalityEventProb k Event := by
  intro hMono k m hk hm
  have hSuccess :=
    fixed_cardinality_event_probability_monotone_of_event_mono
      Event hMono k m hk hm
  linarith

