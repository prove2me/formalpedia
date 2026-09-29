-- Prove2me | solution 1 for tangent_coordinate_projection_frobenius_sq_eq_coordinate_kernel_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T05:38:00.45866+00:00
-- url     : https://prove2.me/submissions/d98bfdd1-c4a2-483a-ba34-acf5864545d0

import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

open scoped Classical BigOperators

private lemma matrixInner_coordinate_right
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma coordinate_projection_kernel_norm_square
    {N r : ℕ} (u : Fin r → Fin N → ℝ)
    (horth : ∀ k l : Fin r,
      ∑ i : Fin N, u k i * u l i = if k = l then 1 else 0)
    (i : Fin N) :
    ∑ a : Fin N, (∑ k : Fin r, u k a * u k i) ^ 2 =
      ∑ k : Fin r, (u k i) ^ 2 := by
  calc
    ∑ a : Fin N, (∑ k : Fin r, u k a * u k i) ^ 2
        = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (u k a * u l a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          ring
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (u k i * u l i) * (∑ a : Fin N, u k a * u l a) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _hl
          rw [Finset.mul_sum]
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (u k i * u l i) * (if k = l then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro l _hl
          rw [horth k l]
    _ = ∑ k : Fin r, (u k i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Finset.sum_eq_single k]
          · simp [pow_two]
          · intro l _hl hne
            have hkne : k ≠ l := fun h => hne h.symm
            simp [hkne]
          · intro hnot
            exact (hnot (Finset.mem_univ k)).elim

private lemma leftSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    leftSingularProjection S (coordinateMatrix i j) a b =
      if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0 := by
  unfold leftSingularProjection coordinateMatrix
  by_cases hbj : b = j
  · subst hbj
    rw [Finset.sum_eq_single i]
    · simp
    · intro x _hx hx
      simp [hx]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · have hzero :
        (∀ x : Fin n₁,
          (if x = i ∧ b = j then (1 : ℝ) else 0) = 0) := by
        intro x
        simp [hbj]
    simp [hbj]

private lemma rightSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    rightSingularProjection S (coordinateMatrix i j) a b =
      if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0 := by
  unfold rightSingularProjection coordinateMatrix
  by_cases hai : a = i
  · subst hai
    rw [Finset.sum_eq_single j]
    · simp
    · intro x _hx hx
      simp [hx]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · have hzero :
        (∀ x : Fin n₂,
          (if a = i ∧ x = j then (1 : ℝ) else 0) = 0) := by
        intro x
        simp [hai]
    simp [hai]

private lemma twoSidedSingularProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    twoSidedSingularProjection S (coordinateMatrix i j) a b =
      (∑ k : Fin r, S.u k a * S.u k i) *
        (∑ k : Fin r, S.v k j * S.v k b) := by
  unfold twoSidedSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [Finset.mul_sum, Finset.sum_mul]
    · intro x _hx hx
      simp [hx]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro x _hx hx
    simp [hx]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma tangentProjection_coordinate_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂)
    (a : Fin n₁) (b : Fin n₂) :
    tangentProjection S (coordinateMatrix i j) a b =
      (if b = j then ∑ k : Fin r, S.u k a * S.u k i else 0) +
        (if a = i then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k a * S.u k i) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  simp [tangentProjection, leftSingularProjection_coordinate_apply,
    rightSingularProjection_coordinate_apply,
    twoSidedSingularProjection_coordinate_apply]

private lemma tangent_coordinate_kernel_diagonal_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    tangentCoordinateKernel S i j i j =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  simp [tangentProjection_coordinate_apply, pow_two]

private lemma coordinate_projection_square_sum
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : α → ℝ) (Q : β → ℝ) (i : α) (j : β)
    (hPi : P i = ∑ a : α, P a ^ 2)
    (hQj : Q j = ∑ b : β, Q b ^ 2) :
    ∑ a : α, ∑ b : β,
      ((if b = j then P a else 0) +
        (if a = i then Q b else 0) - P a * Q b) ^ 2 =
      (∑ a : α, P a ^ 2) +
        (∑ b : β, Q b ^ 2) -
          (∑ a : α, P a ^ 2) * (∑ b : β, Q b ^ 2) := by
  classical
  let A : ℝ := ∑ a : α, P a ^ 2
  let B : ℝ := ∑ b : β, Q b ^ 2
  have hPi' : P i = A := by simpa [A] using hPi
  have hQj' : Q j = B := by simpa [B] using hQj
  have hPQ : (∑ a : α, ∑ b : β, P a ^ 2 * Q b ^ 2) = A * B := by
    dsimp [A, B]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
  have hPQsq : (∑ a : α, ∑ b : β, (P a * Q b) ^ 2) = A * B := by
    calc
      ∑ a : α, ∑ b : β, (P a * Q b) ^ 2
          = ∑ a : α, ∑ b : β, P a ^ 2 * Q b ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = A * B := hPQ
  have hCrossP : (∑ a : α, 2 * P a * (P a * B)) = 2 * A * B := by
    calc
      ∑ a : α, 2 * P a * (P a * B)
          = ∑ a : α, (2 * B) * P a ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            ring
      _ = (2 * B) * (∑ a : α, P a ^ 2) := by
            symm
            rw [Finset.mul_sum]
      _ = 2 * A * B := by
            simp [A, mul_assoc, mul_left_comm, mul_comm]
  have hCrossQ : (∑ b : β, 2 * Q b * (A * Q b)) = 2 * A * B := by
    calc
      ∑ b : β, 2 * Q b * (A * Q b)
          = ∑ b : β, (2 * A) * Q b ^ 2 := by
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = (2 * A) * (∑ b : β, Q b ^ 2) := by
            symm
            rw [Finset.mul_sum]
      _ = 2 * A * B := by
            simp [B, mul_assoc]
  calc
    ∑ a : α, ∑ b : β,
      ((if b = j then P a else 0) +
        (if a = i then Q b else 0) - P a * Q b) ^ 2
        = ∑ a : α, ∑ b : β,
            ((if b = j then P a else 0) ^ 2 +
              (if a = i then Q b else 0) ^ 2 +
              (P a * Q b) ^ 2 +
              2 * (if b = j then P a else 0) *
                (if a = i then Q b else 0) -
              2 * (if b = j then P a else 0) * (P a * Q b) -
              2 * (if a = i then Q b else 0) * (P a * Q b)) := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            ring
    _ = A + B + A * B + 2 * A * B - 2 * A * B - 2 * A * B := by
            simp [hPi', hQj', Finset.sum_add_distrib,
              Finset.sum_sub_distrib]
            rw [hPQsq, hCrossP, hCrossQ]
            ring
    _ = A + B - A * B := by ring
    _ = (∑ a : α, P a ^ 2) +
          (∑ b : β, Q b ^ 2) -
            (∑ a : α, P a ^ 2) * (∑ b : β, Q b ^ 2) := by
            simp [A, B]

private lemma tangent_projection_coordinate_frobenius_sq_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    frobeniusNormSq (tangentProjection S (coordinateMatrix i j)) =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  let P : Fin n₁ → ℝ := fun a => ∑ k : Fin r, S.u k a * S.u k i
  let Q : Fin n₂ → ℝ := fun b => ∑ k : Fin r, S.v k j * S.v k b
  have hPnorm : ∑ a : Fin n₁, P a ^ 2 = ∑ k : Fin r, (S.u k i) ^ 2 := by
    simpa [P, pow_two] using
      coordinate_projection_kernel_norm_square S.u S.u_orthonormal i
  have hQnorm : ∑ b : Fin n₂, Q b ^ 2 = ∑ k : Fin r, (S.v k j) ^ 2 := by
    have hbase :=
      coordinate_projection_kernel_norm_square S.v S.v_orthonormal j
    rw [← hbase]
    apply Finset.sum_congr rfl
    intro b _hb
    congr 1
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hPi : P i = ∑ k : Fin r, (S.u k i) ^ 2 := by
    simp [P, pow_two]
  have hQj : Q j = ∑ k : Fin r, (S.v k j) ^ 2 := by
    simp [Q, pow_two]
  unfold frobeniusNormSq
  calc
    ∑ a : Fin n₁, ∑ b : Fin n₂,
        (tangentProjection S (coordinateMatrix i j) a b) ^ 2
        = ∑ a : Fin n₁, ∑ b : Fin n₂,
            ((if b = j then P a else 0) +
              (if a = i then Q b else 0) - P a * Q b) ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            rw [tangentProjection_coordinate_apply]
    _ = (∑ a : Fin n₁, P a ^ 2) +
          (∑ b : Fin n₂, Q b ^ 2) -
            (∑ a : Fin n₁, P a ^ 2) * (∑ b : Fin n₂, Q b ^ 2) := by
            exact coordinate_projection_square_sum P Q i j
              (hPi.trans hPnorm.symm) (hQj.trans hQnorm.symm)
    _ = (∑ k : Fin r, (S.u k i) ^ 2) +
          (∑ k : Fin r, (S.v k j) ^ 2) -
            (∑ k : Fin r, (S.u k i) ^ 2) *
              (∑ k : Fin r, (S.v k j) ^ 2) := by
            rw [hPnorm, hQnorm]

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNormSq (tangentProjection S (coordinateMatrix i j)) =
        tangentCoordinateKernel S i j i j := by
  intro i j
  rw [tangent_projection_coordinate_frobenius_sq_formula,
    tangent_coordinate_kernel_diagonal_formula]
