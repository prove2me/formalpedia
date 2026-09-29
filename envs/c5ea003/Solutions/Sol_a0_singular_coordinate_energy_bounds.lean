-- Prove2me | solution 1 for a0_singular_coordinate_energy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T17:05:18.175141+00:00
-- url     : https://prove2.me/submissions/ef3d2dbb-6158-4f39-a31b-dc2aff5c2f25

import Mathlib.Data.Fintype.Order
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

open scoped Classical BigOperators

private lemma coherence_coordinate_energy_le
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (u : Fin r → Fin N → ℝ) {μ : ℝ} :
    coherence N r u ≤ μ →
    ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ μ * (r : ℝ) / (N : ℝ) := by
  intro hcoh i
  have hscale_pos : 0 < (N : ℝ) / (r : ℝ) :=
    div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hr)
  have hleSup :
      (∑ k : Fin r, (u k i) ^ 2) ≤
        ⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 :=
    Finite.le_ciSup (f := fun i : Fin N => ∑ k : Fin r, (u k i) ^ 2) i
  have hsup :
      (⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2) ≤
        μ / ((N : ℝ) / (r : ℝ)) := by
    rw [le_div_iff₀ hscale_pos]
    simpa [coherence, mul_comm, mul_left_comm, mul_assoc] using hcoh
  calc
    (∑ k : Fin r, (u k i) ^ 2)
        ≤ μ / ((N : ℝ) / (r : ℝ)) := le_trans hleSup hsup
    _ = μ * (r : ℝ) / (N : ℝ) := by
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
      have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      field_simp [hN', hr']

/-- A0 is exactly a pair of coherence bounds, and unfolding coherence gives
the pointwise coordinate-energy estimates. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) :
    0 < n₁ → 0 < n₂ → 0 < r → A0 S μ₀ →
      (∀ i : Fin n₁,
        ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) ∧
      (∀ j : Fin n₂,
        ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
  intro hn₁ hn₂ hr hA0
  exact ⟨coherence_coordinate_energy_le hn₁ hr S.u hA0.1,
    coherence_coordinate_energy_le hn₂ hr S.v hA0.2⟩
