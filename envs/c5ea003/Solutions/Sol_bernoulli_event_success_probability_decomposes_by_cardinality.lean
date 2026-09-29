-- Prove2me | solution 1 for bernoulli_event_success_probability_decomposes_by_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T04:14:04.585169+00:00
-- url     : https://prove2.me/submissions/8b21b188-6dc2-4b08-b659-d6d13e12b77d

import Definitions.Def_matrix_completion_fixed_cardinality
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators
open Finset

theorem solution {n₁ n₂ : ℕ} (p : ℝ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p Event =
      ∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p *
          fixedCardinalityEventProb k Event := by
  intro hp0 hp1
  set N := n₁ * n₂ with hN
  have hcard : Fintype.card (Fin n₁ × Fin n₂) = N := by
    simp [hN, Fintype.card_prod]
  rw [bernoulliEventProb]
  rw [← Finset.powerset_univ]
  rw [Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  have huniv : (Finset.univ : Finset (Fin n₁ × Fin n₂)).card = N := by
    simp [hN, Fintype.card_prod]
  rw [huniv]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkN : k ≤ N := Nat.lt_succ_iff.mp hk
  have hinner :
      ∑ Omega ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n₁ × Fin n₂)),
          (if Event Omega then bernoulliObservationWeight p Omega else 0)
        = (p ^ k * (1 - p) ^ (N - k)) *
            (((Finset.powersetCard k (Finset.univ : Finset (Fin n₁ × Fin n₂))).filter Event).card : ℝ) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_congr rfl (g := fun _ => p ^ k * (1 - p) ^ (N - k))]
    · rw [Finset.sum_const, nsmul_eq_mul]
      ring
    · intro Omega hΩ
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hΩ
      rw [bernoulliObservationWeight, hΩ.1.2, hcard]
  rw [hinner]
  rw [binomialCardinalityProb, fixedCardinalityEventProb]
  rw [Finset.card_powersetCard, huniv]
  have hch : (0:ℝ) < (Nat.choose N k : ℝ) := by
    have : 0 < Nat.choose N k := Nat.choose_pos hkN
    exact_mod_cast this
  field_simp
