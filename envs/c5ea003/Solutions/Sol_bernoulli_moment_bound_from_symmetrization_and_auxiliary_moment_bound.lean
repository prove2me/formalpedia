-- Prove2me | solution 1 for bernoulli_moment_bound_from_symmetrization_and_auxiliary_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:56:19.787339+00:00
-- url     : https://prove2.me/submissions/b386d38a-a5c3-41fb-8bf5-ebb47439fccb

import Definitions.Def_matrix_completion_rademacher
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    (Csym Crad : ℝ) :
    0 < Csym → 0 < Crad →
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ {n₁ n₂ : ℕ} (p scale : ℝ) (q : ℕ)
        (F G : Finset (Fin n₁ × Fin n₂) → ℝ),
        1 ≤ q →
        bernoulliExpectation p F ≤
          Csym ^ q * bernoulliExpectation p G →
        bernoulliExpectation p G ≤ (Crad * scale) ^ q →
        bernoulliExpectation p F ≤ (Cq * scale) ^ q := by
  intro hCsym hCrad
  refine ⟨Csym * Crad, by positivity, ?_⟩
  intro n₁ n₂ p scale q F G _ hsym hrad
  have hnonneg : 0 ≤ Csym ^ q := by positivity
  calc
    bernoulliExpectation p F ≤
        Csym ^ q * bernoulliExpectation p G := hsym
    _ ≤ Csym ^ q * (Crad * scale) ^ q :=
        mul_le_mul_of_nonneg_left hrad hnonneg
    _ = (Csym * Crad * scale) ^ q := by ring
