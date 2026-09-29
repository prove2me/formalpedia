-- Prove2me | solution 1 for pair_coordinate_cardinality_loss_absorbed_by_beta_shift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T22:37:45.88693+00:00
-- url     : https://prove2.me/submissions/554b48db-8afe-4407-a835-210c32c1cf30

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    (β c : ℝ) (n₁ n₂ : ℕ) :
    2 < β → 0 < c → 0 < n₁ → 0 < n₂ →
    (((Fintype.card
        ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * c) *
        Real.rpow (↑(max n₁ n₂)) (-(β + 4))) ≤
      c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro _hβ hc hn₁ hn₂
  let N : ℕ := max n₁ n₂
  have hN_pos_nat : 0 < N := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hfail_nonneg : 0 ≤ Real.rpow (N : ℝ) (-(β + 4)) :=
    Real.rpow_nonneg (le_of_lt hN_pos) _
  have hcard_nat :
      Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) ≤ N ^ 4 := by
    have hn₁_le : n₁ ≤ N := Nat.le_max_left n₁ n₂
    have hn₂_le : n₂ ≤ N := Nat.le_max_right n₁ n₂
    have hprod : n₁ * n₂ ≤ N * N := Nat.mul_le_mul hn₁_le hn₂_le
    have hprod2 : (n₁ * n₂) * (n₁ * n₂) ≤ (N * N) * (N * N) :=
      Nat.mul_le_mul hprod hprod
    calc
      Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂))
          = (n₁ * n₂) * (n₁ * n₂) := by
              simp [Fintype.card_prod]
      _ ≤ (N * N) * (N * N) := hprod2
      _ = N ^ 4 := by ring
  have hcard_real :
      (Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) ≤
        (N : ℝ) ^ 4 := by
    exact_mod_cast hcard_nat
  have hmul :
      ((Fintype.card
          ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * c) *
          Real.rpow (N : ℝ) (-(β + 4)) ≤
        (((N : ℝ) ^ 4 * c) * Real.rpow (N : ℝ) (-(β + 4))) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard_real hc_nonneg) hfail_nonneg
  have hrpow :
      ((N : ℝ) ^ 4) * Real.rpow (N : ℝ) (-(β + 4)) =
        Real.rpow (N : ℝ) (-β) := by
    calc
      ((N : ℝ) ^ 4) * Real.rpow (N : ℝ) (-(β + 4))
          = Real.rpow (N : ℝ) (4 : ℝ) *
              Real.rpow (N : ℝ) (-(β + 4)) := by
                exact congrArg
                  (fun t => t * Real.rpow (N : ℝ) (-(β + 4)))
                  (Real.rpow_natCast (N : ℝ) 4).symm
      _ = Real.rpow (N : ℝ) ((4 : ℝ) + (-(β + 4))) := by
                exact (Real.rpow_add hN_pos (4 : ℝ) (-(β + 4))).symm
      _ = Real.rpow (N : ℝ) (-β) := by
                congr 1
                ring
  have htarget :
      (((N : ℝ) ^ 4 * c) * Real.rpow (N : ℝ) (-(β + 4))) =
        c * Real.rpow (N : ℝ) (-β) := by
    calc
      (((N : ℝ) ^ 4 * c) * Real.rpow (N : ℝ) (-(β + 4)))
          = c * (((N : ℝ) ^ 4) * Real.rpow (N : ℝ) (-(β + 4))) := by
              ring
      _ = c * Real.rpow (N : ℝ) (-β) := by
              rw [hrpow]
  simpa [N] using le_trans hmul (le_of_eq htarget)
