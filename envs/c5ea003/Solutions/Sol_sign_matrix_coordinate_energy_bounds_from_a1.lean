-- Prove2me | solution 1 for sign_matrix_coordinate_energy_bounds_from_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T17:08:11.815881+00:00
-- url     : https://prove2.me/submissions/f8b832c7-de3c-4c25-a60e-45939aae9d52

import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

open scoped Classical BigOperators

private lemma signMatrix_row_sq_sum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) :
    ∑ j : Fin n₂, (signMatrix S i j) ^ 2 =
      ∑ k : Fin r, (S.u k i) ^ 2 := by
  calc
    ∑ j : Fin n₂, (signMatrix S i j) ^ 2
        = ∑ j : Fin n₂, ∑ k : Fin r, ∑ l : Fin r,
            (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]
          simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          ring
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (S.u k i * S.u l i) *
            (∑ j : Fin n₂, S.v k j * S.v l j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _hl
          rw [Finset.mul_sum]
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (S.u k i * S.u l i) * (if k = l then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          rw [S.v_orthonormal k l]
    _ = ∑ k : Fin r, (S.u k i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_eq_single k]
          · simp [pow_two]
          · intro l _hl hne
            have hkne : k ≠ l := fun h => hne h.symm
            simp [hkne]
          · intro hnot
            exact (hnot (Finset.mem_univ k)).elim

private lemma signMatrix_col_sq_sum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (j : Fin n₂) :
    ∑ i : Fin n₁, (signMatrix S i j) ^ 2 =
      ∑ k : Fin r, (S.v k j) ^ 2 := by
  calc
    ∑ i : Fin n₁, (signMatrix S i j) ^ 2
        = ∑ i : Fin n₁, ∑ k : Fin r, ∑ l : Fin r,
            (S.v k j * S.v l j) * (S.u k i * S.u l i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          simp [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]
          simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          ring
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (S.v k j * S.v l j) *
            (∑ i : Fin n₁, S.u k i * S.u l i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _hl
          rw [Finset.mul_sum]
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (S.v k j * S.v l j) * (if k = l then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          rw [S.u_orthonormal k l]
    _ = ∑ k : Fin r, (S.v k j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_eq_single k]
          · simp [pow_two]
          · intro l _hl hne
            have hkne : k ≠ l := fun h => hne h.symm
            simp [hkne]
          · intro hnot
            exact (hnot (Finset.mem_univ k)).elim

private lemma signMatrix_entry_sq_bound_from_a1
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₁ : ℝ) :
    0 < n₁ → 0 < n₂ → 1 ≤ μ₁ → A1 S μ₁ →
      ∀ i : Fin n₁, ∀ j : Fin n₂,
        (signMatrix S i j) ^ 2 ≤
          μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  intro hn₁ hn₂ hμ₁ hA1 i j
  let B : ℝ := μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
  have hden_nonneg : 0 ≤ (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hratio_nonneg :
      0 ≤ (r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by
    exact div_nonneg (Nat.cast_nonneg _) hden_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (le_trans zero_le_one hμ₁) (Real.sqrt_nonneg _)
  have habs_le_B : |signMatrix S i j| ≤ B := by
    simpa [B] using hA1 i j
  have habs : |signMatrix S i j| ≤ |B| := by
    simpa [abs_of_nonneg hB_nonneg] using habs_le_B
  have hsquare : (signMatrix S i j) ^ 2 ≤ B ^ 2 := by
    exact sq_le_sq.mpr habs
  have hB_sq :
      B ^ 2 = μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt hratio_nonneg]
  simpa [hB_sq] using hsquare

theorem solution :
    ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₁ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₁ → A1 S μ₁ →
      (∀ i : Fin n₁,
        ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₁ ^ 2 * (r : ℝ) / (n₁ : ℝ)) ∧
      (∀ j : Fin n₂,
        ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ)) := by
  intro n₁ n₂ r M μ₁ S hn₁ hn₂ _hr hμ₁ hA1
  have hentry := signMatrix_entry_sq_bound_from_a1 S μ₁ hn₁ hn₂ hμ₁ hA1
  constructor
  · intro i
    have hsum :
        ∑ j : Fin n₂, (signMatrix S i j) ^ 2 ≤
          ∑ j : Fin n₂, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
      exact Finset.sum_le_sum fun j _hj => hentry i j
    have hconst :
        (∑ j : Fin n₂, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) =
          μ₁ ^ 2 * (r : ℝ) / (n₁ : ℝ) := by
      have hn₁_ne : (n₁ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn₁)
      have hn₂_ne : (n₂ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn₂)
      simp
      field_simp [hn₁_ne, hn₂_ne]
    calc
      ∑ k : Fin r, (S.u k i) ^ 2
          = ∑ j : Fin n₂, (signMatrix S i j) ^ 2 := (signMatrix_row_sq_sum S i).symm
      _ ≤ ∑ j : Fin n₂, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := hsum
      _ = μ₁ ^ 2 * (r : ℝ) / (n₁ : ℝ) := hconst
  · intro j
    have hsum :
        ∑ i : Fin n₁, (signMatrix S i j) ^ 2 ≤
          ∑ i : Fin n₁, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
      exact Finset.sum_le_sum fun i _hi => hentry i j
    have hconst :
        (∑ i : Fin n₁, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) =
          μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ) := by
      have hn₁_ne : (n₁ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn₁)
      have hn₂_ne : (n₂ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn₂)
      simp
      field_simp [hn₁_ne, hn₂_ne]
    calc
      ∑ k : Fin r, (S.v k j) ^ 2
          = ∑ i : Fin n₁, (signMatrix S i j) ^ 2 := (signMatrix_col_sq_sum S j).symm
      _ ≤ ∑ i : Fin n₁, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := hsum
      _ = μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ) := hconst
