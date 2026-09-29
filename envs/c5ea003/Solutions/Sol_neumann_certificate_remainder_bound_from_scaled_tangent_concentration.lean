-- Prove2me | solution 1 for neumann_certificate_remainder_bound_from_scaled_tangent_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T05:11:13.784182+00:00
-- url     : https://prove2.me/submissions/ba59e5fb-fa05-4536-a6d5-e41e717ba3bf

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Self-contained assembly for `fe401eed`:
geometric Neumann certificate tail bound from scaled tangent concentration.
CR2009 (arXiv:0805.4471) Lemma 4.8, eq (4.18) with k0 = 3; §6.3 geometric-series proof.
All helper lemmas inlined verbatim from the Scratch dependency chain.
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Matrix Real Filter Topology LinearMap

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

-- =================== Scratch_contraction ===================
theorem ker_idem {N r : Nat} (u : Fin r → (Fin N → ℝ))
    (horth : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0)
    (i b : Fin N) :
    (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ k : Fin r, u k i * u k b := by
  have e1 : (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b) := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ a : Fin N, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; rw [horth k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, u k i * u l b * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then u k i * u l b else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

theorem left_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X) = leftSingularProjection S X := by
  funext i j
  unfold leftSingularProjection
  have : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
      = ∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * X a j := by
    have hL : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
        = ∑ a : Fin n1, (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
              (∑ k : Fin r, S.u k c * S.u k a)) * X a j := by
      have hLeft : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
          = ∑ c : Fin n1, ∑ a : Fin n1,
              (∑ k : Fin r, S.u k i * S.u k c) * (∑ k : Fin r, S.u k c * S.u k a) * X a j := by
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      have hRight : (∑ a : Fin n1, (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
              (∑ k : Fin r, S.u k c * S.u k a)) * X a j)
          = ∑ a : Fin n1, ∑ c : Fin n1,
              (∑ k : Fin r, S.u k i * S.u k c) * (∑ k : Fin r, S.u k c * S.u k a) * X a j := by
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_mul]
      rw [hLeft, hRight, Finset.sum_comm]
    rw [hL]
    apply Finset.sum_congr rfl; intro a _
    rw [ker_idem S.u S.u_orthonormal i a]
  exact this

theorem right_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X) = rightSingularProjection S X := by
  funext i j
  unfold rightSingularProjection
  have hR : (∑ b : Fin n2, (∑ c : Fin n2, X i c * (∑ l : Fin r, S.v l c * S.v l b)) *
              (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ c : Fin n2, X i c * (∑ b : Fin n2,
            (∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
    have hLeft : (∑ b : Fin n2, (∑ c : Fin n2, X i c * (∑ l : Fin r, S.v l c * S.v l b)) *
              (∑ l : Fin r, S.v l b * S.v l j))
        = ∑ b : Fin n2, ∑ c : Fin n2,
            X i c * ((∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro c _; ring
    have hRight : (∑ c : Fin n2, X i c * (∑ b : Fin n2,
            (∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)))
        = ∑ c : Fin n2, ∑ b : Fin n2,
            X i c * ((∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
      apply Finset.sum_congr rfl; intro c _
      rw [Finset.mul_sum]
    rw [hLeft, hRight, Finset.sum_comm]
  rw [hR]
  apply Finset.sum_congr rfl; intro c _
  rw [ker_idem S.v S.v_orthonormal c j]

theorem two_eq_left_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = leftSingularProjection S (rightSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem two_eq_right_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = rightSingularProjection S (leftSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

theorem left_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B) = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  unfold leftSingularProjection
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem left_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B) = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  unfold leftSingularProjection
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem right_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B) = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  unfold rightSingularProjection
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem right_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B) = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  unfold rightSingularProjection
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem left_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_left_right S X, left_left S (rightSingularProjection S X)]

theorem right_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_right_left S X, right_right S (leftSingularProjection S X)]

theorem left_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (tangentProjection S X) = leftSingularProjection S X := by
  unfold tangentProjection
  rw [left_sub, left_add, left_left, ← two_eq_left_right, left_two]
  abel

theorem right_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (tangentProjection S X) = rightSingularProjection S X := by
  unfold tangentProjection
  rw [right_sub, right_add, right_right, ← two_eq_right_left, right_two]
  abel

theorem two_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (tangentProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_left_right S (tangentProjection S X), right_tangent, ← two_eq_left_right]

theorem tangent_idem {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  conv_lhs => rw [tangentProjection]
  rw [left_tangent, right_tangent, two_tangent]
  rfl

-- ===== self-adjoint + coordinate (copied from Thm file) =====

theorem matrixInner_coordinateMatrix {n1 n2 : Nat} (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _; simp [ha]
  · intro h; simp at h

theorem tangentProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner X (tangentProjection S Y) = matrixInner (tangentProjection S X) Y := by
  unfold matrixInner tangentProjection leftSingularProjection rightSingularProjection
    twoSidedSingularProjection
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have h1 : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j) := by
    have hLn : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
        = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2,
            (∑ k, S.u k i * S.u k a) * (X i j * Y a j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    have hRn : (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j)
        = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2,
            (∑ k, S.u k i * S.u k a) * (X a j * Y i j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hLn, hRn, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have hk : (∑ k, S.u k a * S.u k i) = (∑ k, S.u k i * S.u k a) := by
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hk]
  have h2 : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    apply Finset.sum_congr rfl; intro i _
    have hLn : (∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
        = ∑ j : Fin n2, ∑ b : Fin n2, (∑ l, S.v l b * S.v l j) * (X i j * Y i b) := by
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    have hRn : (∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j)
        = ∑ j : Fin n2, ∑ b : Fin n2, (∑ l, S.v l b * S.v l j) * (X i b * Y i j) := by
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    rw [hLn, hRn, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    have hk : (∑ l, S.v l j * S.v l b) = (∑ l, S.v l b * S.v l j) := by
      apply Finset.sum_congr rfl; intro l _; ring
    rw [hk]
  have h3 : (∑ i : Fin n1, ∑ j : Fin n2,
        X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))
      = (∑ i : Fin n1, ∑ j : Fin n2,
        (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    have hLn : (∑ i : Fin n1, ∑ j : Fin n2,
          X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))
        = ∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X i j * Y a b) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    have hRn : (∑ i : Fin n1, ∑ j : Fin n2,
          (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j)
        = ∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X a b * Y i j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    rw [hLn, hRn]
    rw [show (∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X i j * Y a b))
        = ∑ q : (Fin n1 × Fin n2) × (Fin n1 × Fin n2),
            (∑ k, S.u k q.1.1 * S.u k q.2.1) * (∑ l, S.v l q.2.2 * S.v l q.1.2)
              * (X q.1.1 q.1.2 * Y q.2.1 q.2.2) from by
          simp_rw [Fintype.sum_prod_type]]
    rw [show (∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X a b * Y i j))
        = ∑ q : (Fin n1 × Fin n2) × (Fin n1 × Fin n2),
            (∑ k, S.u k q.1.1 * S.u k q.2.1) * (∑ l, S.v l q.2.2 * S.v l q.1.2)
              * (X q.2.1 q.2.2 * Y q.1.1 q.1.2) from by
          simp_rw [Fintype.sum_prod_type]]
    apply Finset.sum_nbij' (i := fun q => (q.2, q.1)) (j := fun q => (q.2, q.1))
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
    · intro p _
      have hku : (∑ k, S.u k p.2.1 * S.u k p.1.1) = (∑ k, S.u k p.1.1 * S.u k p.2.1) := by
        apply Finset.sum_congr rfl; intro k _; ring
      have hlv : (∑ l, S.v l p.1.2 * S.v l p.2.2) = (∑ l, S.v l p.2.2 * S.v l p.1.2) := by
        apply Finset.sum_congr rfl; intro l _; ring
      show _ = _
      simp only
      rw [hku, hlv]
  have hdistL : (∑ i : Fin n1, ∑ j : Fin n2,
        X i j * (((∑ a, (∑ k, S.u k i * S.u k a) * Y a j)
                  + (∑ b, Y i b * (∑ l, S.v l b * S.v l j))
                  - (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))))
      = (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
        + (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
        - (∑ i : Fin n1, ∑ j : Fin n2,
            X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hdistR : (∑ i : Fin n1, ∑ j : Fin n2,
        (((∑ a, (∑ k, S.u k i * S.u k a) * X a j)
                  + (∑ b, X i b * (∑ l, S.v l b * S.v l j))
                  - (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)))) * Y i j)
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j)
        + (∑ i : Fin n1, ∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j)
        - (∑ i : Fin n1, ∑ j : Fin n2,
            (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hdistL, hdistR, h1, h2, h3]

-- ===== norm helpers =====

theorem matrixInner_self {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    matrixInner X X = frobeniusNormSq X := by
  unfold matrixInner frobeniusNormSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem frobeniusNormSq_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ frobeniusNormSq X :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem frobeniusNormSq_eq_sq {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    frobeniusNormSq X = frobeniusNorm X ^ 2 := by
  unfold frobeniusNorm
  rw [Real.sq_sqrt (frobeniusNormSq_nonneg X)]

/-- Cauchy–Schwarz, squared form, for the Frobenius inner product. -/
theorem matrixInner_sq_le {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    matrixInner X Y ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
  have hfold : (∑ i : Fin n1, ∑ j : Fin n2, X i j * Y i j)
        = ∑ q : Fin n1 × Fin n2, X q.1 q.2 * Y q.1 q.2 :=
    (Fintype.sum_prod_type (fun q => X q.1 q.2 * Y q.1 q.2)).symm
  have hfoldX : (∑ i : Fin n1, ∑ j : Fin n2, X i j ^ 2)
        = ∑ q : Fin n1 × Fin n2, X q.1 q.2 ^ 2 :=
    (Fintype.sum_prod_type (fun q => X q.1 q.2 ^ 2)).symm
  have hfoldY : (∑ i : Fin n1, ∑ j : Fin n2, Y i j ^ 2)
        = ∑ q : Fin n1 × Fin n2, Y q.1 q.2 ^ 2 :=
    (Fintype.sum_prod_type (fun q => Y q.1 q.2 ^ 2)).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n1 × Fin n2))
      (fun q => X q.1 q.2) (fun q => Y q.1 q.2)
  unfold matrixInner frobeniusNormSq
  rw [hfold, hfoldX, hfoldY]
  exact hcs


-- =================== Scratch_invert ===================
variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-! ## P_T linearity (add + smul) -/

theorem left_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    leftSingularProjection S (c • X) = c • leftSingularProjection S X := by
  funext i j
  unfold leftSingularProjection
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; ring

theorem right_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    rightSingularProjection S (c • X) = c • rightSingularProjection S X := by
  funext i j
  unfold rightSingularProjection
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem two_smul' (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (c • X) = c • twoSidedSingularProjection S X := by
  funext i j
  unfold twoSidedSingularProjection
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem two_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A + B)
      = twoSidedSingularProjection S A + twoSidedSingularProjection S B := by
  funext i j
  unfold twoSidedSingularProjection
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem tangent_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    tangentProjection S (A + B) = tangentProjection S A + tangentProjection S B := by
  unfold tangentProjection
  rw [left_add, right_add, two_add]; abel

theorem tangent_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    tangentProjection S (c • X) = c • tangentProjection S X := by
  unfold tangentProjection
  rw [left_smul, right_smul, two_smul']
  rw [smul_sub, smul_add]

theorem two_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A - B)
      = twoSidedSingularProjection S A - twoSidedSingularProjection S B := by
  funext i j
  unfold twoSidedSingularProjection
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem tangent_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    tangentProjection S (A - B) = tangentProjection S A - tangentProjection S B := by
  unfold tangentProjection
  rw [left_sub, right_sub, two_sub]; abel

/-- P_T packaged as an ℝ-linear map. -/
theorem sampling_add (Omega : Finset (Fin n1 × Fin n2)) (A B : RealMatrix n1 n2) :
    samplingProjection Omega (A + B)
      = samplingProjection Omega A + samplingProjection Omega B := by
  funext i j
  unfold samplingProjection
  simp only [Matrix.add_apply]
  by_cases h : (i, j) ∈ Omega <;> simp [h]

theorem sampling_smul (Omega : Finset (Fin n1 × Fin n2)) (c : ℝ) (X : RealMatrix n1 n2) :
    samplingProjection Omega (c • X) = c • samplingProjection Omega X := by
  funext i j
  unfold samplingProjection
  simp only [Matrix.smul_apply, smul_eq_mul]
  by_cases h : (i, j) ∈ Omega <;> simp [h]

/-- P_Ω is self-adjoint w.r.t. the Frobenius inner product. -/
theorem sampling_selfAdjoint (Omega : Finset (Fin n1 × Fin n2)) (X Y : RealMatrix n1 n2) :
    matrixInner X (samplingProjection Omega Y)
      = matrixInner (samplingProjection Omega X) Y := by
  unfold matrixInner samplingProjection
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  by_cases h : (i, j) ∈ Omega <;> simp [h]

/-- For a matrix supported on Ω, P_Ω is the identity. -/
theorem sampling_of_vanishesOutside (Omega : Finset (Fin n1 × Fin n2))
    (Z : RealMatrix n1 n2) (hZ : VanishesOutside Omega Z) :
    samplingProjection Omega Z = Z := by
  funext i j
  unfold samplingProjection
  by_cases h : (i, j) ∈ Omega
  · simp [h]
  · simp [h, hZ i j h]

/-! ## E = signMatrix S ∈ T  (P_T E = E) -/

theorem left_signMatrix (S : SVD M r) :
    leftSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold leftSingularProjection signMatrix
  -- signMatrix a j = ∑ l, u l a * v l j
  have hsm : ∀ a : Fin n1, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) a j
      = ∑ l : Fin r, S.u l a * S.v l j := by
    intro a
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  -- LHS = ∑ a (∑ k u_k i u_k a)(∑ l u_l a v_l j)
  -- = ∑ k u_k i v_k j  (orthonormality of u)
  have hgoal : (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
        = ∑ a : Fin n1, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j) := by
      apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ k : Fin r, ∑ a : Fin n1, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n1, S.u k a * S.u l a) := by
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
    rw [e2]
    have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n1, S.u k a * S.u l a))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (if k = l then 1 else 0) := by
      apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
      rw [S.u_orthonormal k l]
    rw [e3]
    apply Finset.sum_congr rfl; intro k _
    have : (∑ l : Fin r, S.u k i * S.v l j * (if k = l then 1 else 0))
        = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
      apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

theorem right_signMatrix (S : SVD M r) :
    rightSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold rightSingularProjection signMatrix
  have hsm : ∀ b : Fin n2, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) i b
      = ∑ l : Fin r, S.u l i * S.v l b := by
    intro b
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _; rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  have hgoal : (∑ b : Fin n2, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ b : Fin n2, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
        = ∑ b : Fin n2, ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j) := by
      apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ l : Fin r, ∑ b : Fin n2, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n2, S.v l b * S.v k b) := by
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e2]
    have e3 : (∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n2, S.v l b * S.v k b))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (if l = k then 1 else 0) := by
      apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro k _
      rw [S.v_orthonormal l k]
    rw [e3]
    apply Finset.sum_congr rfl; intro l _
    have : (∑ k : Fin r, S.u l i * S.v k j * (if l = k then 1 else 0))
        = ∑ k : Fin r, (if l = k then S.u l i * S.v k j else 0) := by
      apply Finset.sum_congr rfl; intro k _; by_cases h : l = k <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

theorem two_signMatrix (S : SVD M r) :
    twoSidedSingularProjection S (signMatrix S) = signMatrix S := by
  -- two = left of (right of signMatrix) = left of signMatrix = signMatrix
  rw [two_eq_left_right, right_signMatrix, left_signMatrix]

theorem tangent_signMatrix (S : SVD M r) :
    tangentProjection S (signMatrix S) = signMatrix S := by
  unfold tangentProjection
  rw [left_signMatrix, right_signMatrix, two_signMatrix]
  abel

/-! ## Frobenius norm helpers -/

theorem frobeniusNormSq_eq_zero_iff' (X : RealMatrix n1 n2) :
    frobeniusNormSq X = 0 ↔ X = 0 := by
  unfold frobeniusNormSq
  constructor
  · intro h
    funext i j
    have hnn : ∀ a ∈ (Finset.univ : Finset (Fin n1)),
        (0 : Real) ≤ ∑ b : Fin n2, X a b ^ 2 :=
      fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)
    have h1 : ∀ a ∈ (Finset.univ : Finset (Fin n1)),
        (∑ b : Fin n2, X a b ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
    have h2 := h1 i (Finset.mem_univ i)
    have hnn2 : ∀ b ∈ (Finset.univ : Finset (Fin n2)), (0 : Real) ≤ X i b ^ 2 :=
      fun b _ => sq_nonneg _
    have h3 : ∀ b ∈ (Finset.univ : Finset (Fin n2)), X i b ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn2).1 h2
    have h4 := h3 j (Finset.mem_univ j)
    have : X i j = 0 := by nlinarith [h4]
    simpa using this
  · intro h; subst h; simp

theorem frobeniusNorm_smul' (c : Real) (X : RealMatrix n1 n2) :
    frobeniusNorm (c • X) = |c| * frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  have : (∑ i : Fin n1, ∑ j : Fin n2, (c • X) i j ^ 2)
      = c ^ 2 * ∑ i : Fin n1, ∑ j : Fin n2, X i j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : (c • X) i j = c * X i j := rfl
    rw [this]; ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]


-- =================== Scratch_invert2 (matrixInner_sub_right / zero_right) ===================
variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}
theorem matrixInner_sub_right (X A B : RealMatrix n1 n2) :
    matrixInner X (A - B) = matrixInner X A - matrixInner X B := by
  unfold matrixInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Matrix.sub_apply]; ring

theorem matrixInner_zero_right (X : RealMatrix n1 n2) :
    matrixInner X (0 : RealMatrix n1 n2) = 0 := by
  unfold matrixInner; simp


-- =================== Scratch_neumann1 ===================
variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-! ## Per-entry bound by Frobenius norm -/

theorem abs_entry_le_frobeniusNorm (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    |X i j| ≤ frobeniusNorm X := by
  unfold frobeniusNorm
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  -- X i j ^ 2 ≤ ∑ ∑ X a b ^ 2
  have hj : X i j ^ 2 ≤ ∑ b : Fin n2, X i b ^ 2 := by
    refine Finset.single_le_sum (f := fun b => X i b ^ 2) ?_ (Finset.mem_univ j)
    intro b _; exact sq_nonneg _
  have hi : (∑ b : Fin n2, X i b ^ 2) ≤ ∑ a : Fin n1, ∑ b : Fin n2, X a b ^ 2 := by
    refine Finset.single_le_sum (f := fun a => ∑ b : Fin n2, X a b ^ 2) ?_ (Finset.mem_univ i)
    intro a _; exact Finset.sum_nonneg (fun b _ => sq_nonneg _)
  exact le_trans hj hi

/-! ## H = neumannErrorOperator: basic algebra -/

/-- `H X` depends on `X` only through `P_T X`. -/
theorem neumannErrorOperator_comp_tangent (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : ℝ) (X : RealMatrix n1 n2) :
    neumannErrorOperator Omega S p (tangentProjection S X)
      = neumannErrorOperator Omega S p X := by
  unfold neumannErrorOperator
  rw [tangent_idem]

/-- `H X` always lands in `T`. -/
theorem neumannErrorOperator_mem (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : ℝ) (X : RealMatrix n1 n2) :
    tangentProjection S (neumannErrorOperator Omega S p X)
      = neumannErrorOperator Omega S p X := by
  unfold neumannErrorOperator
  rw [tangent_sub, tangent_idem, tangent_smul, tangent_idem]

/-- On `T`, `H X = X - p⁻¹ P_T(P_Ω X)`. -/
theorem neumannErrorOperator_of_mem (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : ℝ) (X : RealMatrix n1 n2)
    (hX : tangentProjection S X = X) :
    neumannErrorOperator Omega S p X
      = X - p⁻¹ • tangentProjection S (samplingProjection Omega X) := by
  unfold neumannErrorOperator
  rw [hX]

/-- Linearity in the sense of additivity of `H` (it is `P_T ∘ (id - p⁻¹ P_Ω) ∘ P_T`). -/
theorem neumannErrorOperator_add (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : ℝ) (A B : RealMatrix n1 n2) :
    neumannErrorOperator Omega S p (A + B)
      = neumannErrorOperator Omega S p A + neumannErrorOperator Omega S p B := by
  unfold neumannErrorOperator
  rw [tangent_add, sampling_add, tangent_add, smul_add]
  abel

theorem neumannErrorOperator_smul (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p c : ℝ) (X : RealMatrix n1 n2) :
    neumannErrorOperator Omega S p (c • X)
      = c • neumannErrorOperator Omega S p X := by
  unfold neumannErrorOperator
  rw [tangent_smul, sampling_smul, tangent_smul, smul_comm p⁻¹ c, smul_sub]

/-! ## Contraction on T from concentration -/

/-- The contraction estimate: for `X ∈ T`,
`‖H X‖_F ≤ (1/2) ‖X‖_F`, using `0 < p` and concentration at `ε = 1/2`. -/
theorem neumannErrorOperator_contraction (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : ℝ) (hp : 0 < p)
    (hconc : TangentSamplingConcentration Omega S p ((1 : ℝ) / 2))
    (X : RealMatrix n1 n2) (hX : tangentProjection S X = X) :
    frobeniusNorm (neumannErrorOperator Omega S p X) ≤ (1 / 2) * frobeniusNorm X := by
  -- H X = X - p⁻¹ P_T(P_Ω X) = -p⁻¹ • (P_T(P_Ω X) - p•X)
  have hHX : neumannErrorOperator Omega S p X
      = (-p⁻¹) • (tangentProjection S (samplingProjection Omega X) - p • X) := by
    rw [neumannErrorOperator_of_mem Omega S p X hX]
    rw [smul_sub]
    rw [neg_smul, neg_smul]
    rw [smul_smul]
    rw [inv_mul_cancel₀ (ne_of_gt hp), one_smul]
    abel
  rw [hHX, frobeniusNorm_smul']
  have habs : |(-p⁻¹)| = p⁻¹ := by
    rw [abs_neg, abs_of_pos (inv_pos.mpr hp)]
  rw [habs]
  -- concentration: ‖P_T(P_Ω X) - p•X‖ ≤ (1/2) p ‖X‖
  have hkey := hconc X hX
  -- p⁻¹ * ‖...‖ ≤ p⁻¹ * ((1/2) * p * ‖X‖) = (1/2) ‖X‖
  have hpinv : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp)
  calc p⁻¹ * frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
      ≤ p⁻¹ * ((1 / 2) * p * frobeniusNorm X) := by
        apply mul_le_mul_of_nonneg_left hkey hpinv
    _ = (1 / 2) * frobeniusNorm X := by
        rw [show p⁻¹ * ((1 / 2) * p * frobeniusNorm X)
            = (1 / 2) * (p⁻¹ * p) * frobeniusNorm X by ring,
          inv_mul_cancel₀ (ne_of_gt hp)]
        ring


-- =================== Scratch_neumann2 ===================
variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-! ## normalProjection: self-adjoint, idempotent, contraction -/

theorem normal_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    normalProjection S (A + B) = normalProjection S A + normalProjection S B := by
  unfold normalProjection; rw [tangent_add]; abel

theorem normal_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    normalProjection S (c • X) = c • normalProjection S X := by
  unfold normalProjection; rw [tangent_smul, smul_sub]

theorem tangent_normal (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (normalProjection S X) = 0 := by
  unfold normalProjection
  rw [tangent_sub, tangent_idem, sub_self]

theorem normalProjection_selfAdjoint (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner X (normalProjection S Y) = matrixInner (normalProjection S X) Y := by
  unfold normalProjection
  rw [matrixInner_sub_right]
  have hsym : matrixInner (X - tangentProjection S X) Y
      = matrixInner Y (X - tangentProjection S X) := by
    unfold matrixInner; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hsym, matrixInner_sub_right]
  rw [tangentProjection_selfAdjoint S X Y]
  have hsym2 : matrixInner X Y = matrixInner Y X := by
    unfold matrixInner; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  have hsym3 : matrixInner (tangentProjection S X) Y = matrixInner Y (tangentProjection S X) := by
    unfold matrixInner; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hsym2, hsym3]

theorem normal_idem (S : SVD M r) (X : RealMatrix n1 n2) :
    normalProjection S (normalProjection S X) = normalProjection S X := by
  unfold normalProjection
  conv_lhs => rw [tangent_sub, tangent_idem, sub_self, sub_zero]

/-- `P_{T⊥}` is a Frobenius contraction. -/
theorem normalProjection_contraction (S : SVD M r) (X : RealMatrix n1 n2) :
    frobeniusNorm (normalProjection S X) ≤ frobeniusNorm X := by
  set Y := normalProjection S X with hY
  -- ‖Y‖² = ⟨Y,Y⟩ = ⟨X, P_{T⊥}(P_{T⊥}X)⟩ = ⟨X,Y⟩
  have hself : matrixInner Y Y = matrixInner X Y := by
    have hsa := normalProjection_selfAdjoint S X Y
    rw [hY] at hsa
    rw [normal_idem] at hsa
    rw [hY]; exact hsa.symm
  have hYY : frobeniusNormSq Y = matrixInner X Y := by
    rw [← matrixInner_self Y, hself]
  have hcs : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y :=
    matrixInner_sq_le X Y
  have hYYnn : 0 ≤ frobeniusNormSq Y := frobeniusNormSq_nonneg Y
  have hXXnn : 0 ≤ frobeniusNormSq X := frobeniusNormSq_nonneg X
  have hsqle : frobeniusNormSq Y ≤ frobeniusNormSq X := by
    rcases eq_or_lt_of_le hYYnn with h0 | hpos
    · rw [← h0]; exact hXXnn
    · have hsq : (frobeniusNormSq Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
        calc (frobeniusNormSq Y) ^ 2 = (matrixInner X Y) ^ 2 := by rw [hYY]
          _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hcs
      have : frobeniusNormSq Y * frobeniusNormSq Y ≤ frobeniusNormSq X * frobeniusNormSq Y := by
        calc frobeniusNormSq Y * frobeniusNormSq Y = (frobeniusNormSq Y) ^ 2 := by ring
          _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hsq
      exact le_of_mul_le_mul_right this hpos
  -- pass to frobeniusNorm via monotone sqrt
  unfold frobeniusNorm
  exact Real.sqrt_le_sqrt hsqle

/-! ## Iterates of H -/

/-- All iterates `H^[k] E` lie in `T`. -/
theorem neumannIterate_mem (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : ℝ)
    (k : ℕ) : tangentProjection S (neumannIterate Omega S p k) = neumannIterate Omega S p k := by
  induction k with
  | zero =>
      simp only [neumannIterate, Function.iterate_zero_apply]
      exact tangent_signMatrix S
  | succ k ih =>
      simp only [neumannIterate, Function.iterate_succ_apply']
      exact neumannErrorOperator_mem Omega S p _

/-- Geometric decay: `‖H^[k] E‖_F ≤ (1/2)^k ‖E‖_F`. -/
theorem neumannIterate_geometric (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : ℝ)
    (hp : 0 < p) (hconc : TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) (k : ℕ) :
    frobeniusNorm (neumannIterate Omega S p k)
      ≤ (1 / 2) ^ k * frobeniusNorm (signMatrix S) := by
  induction k with
  | zero =>
      simp only [neumannIterate, Function.iterate_zero_apply, pow_zero, one_mul]
      exact le_refl _
  | succ k ih =>
      simp only [neumannIterate, Function.iterate_succ_apply']
      -- ‖H (H^[k]E)‖ ≤ (1/2) ‖H^[k]E‖ ≤ (1/2)(1/2)^k ‖E‖
      have hmem := neumannIterate_mem Omega S p k
      have hstep := neumannErrorOperator_contraction Omega S p hp hconc
        (neumannIterate Omega S p k) hmem
      have hnn : (0:ℝ) ≤ 1 / 2 := by norm_num
      calc frobeniusNorm (neumannErrorOperator Omega S p (neumannIterate Omega S p k))
          ≤ (1 / 2) * frobeniusNorm (neumannIterate Omega S p k) := hstep
        _ ≤ (1 / 2) * ((1 / 2) ^ k * frobeniusNorm (signMatrix S)) :=
            mul_le_mul_of_nonneg_left ih hnn
        _ = (1 / 2) ^ (k + 1) * frobeniusNorm (signMatrix S) := by ring


-- =================== Scratch_s29probe ===================
theorem euclidean_norm_sq (x : EuclideanSpace ℝ (Fin n2)) :
    ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  apply Finset.sum_congr rfl; intro j _
  rw [Real.norm_eq_abs, sq_abs]

theorem toEuclideanLin_apply_eq (X : RealMatrix n1 n2) (x : EuclideanSpace ℝ (Fin n2))
    (i : Fin n1) : (toEuclideanLin X) x i = ∑ j, X i j * x j := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

/-- Pointwise: ‖(toEuclideanLin X) x‖ ≤ frobeniusNorm X * ‖x‖ (Cauchy–Schwarz, row by row). -/
theorem toEuclideanLin_apply_le_frobenius (X : RealMatrix n1 n2)
    (x : EuclideanSpace ℝ (Fin n2)) :
    ‖(toEuclideanLin X) x‖ ≤ frobeniusNorm X * ‖x‖ := by
  -- square both sides; both nonneg
  have hx2 : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := euclidean_norm_sq x
  have hlhs2 : ‖(toEuclideanLin X) x‖ ^ 2 = ∑ i, (∑ j, X i j * x j) ^ 2 := by
    rw [euclidean_norm_sq]
    apply Finset.sum_congr rfl; intro i _
    rw [toEuclideanLin_apply_eq]
  -- per-row Cauchy–Schwarz: (∑ j Xij xj)² ≤ (∑ j Xij²)(∑ j xj²)
  have hrow : ∀ i, (∑ j, X i j * x j) ^ 2 ≤ (∑ j, (X i j) ^ 2) * (∑ j, (x j) ^ 2) := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => X i j) (fun j => x j)
    simpa using h
  have hsum : ∑ i, (∑ j, X i j * x j) ^ 2 ≤ (∑ i, ∑ j, (X i j) ^ 2) * (∑ j, (x j) ^ 2) := by
    calc ∑ i, (∑ j, X i j * x j) ^ 2
        ≤ ∑ i, (∑ j, (X i j) ^ 2) * (∑ j, (x j) ^ 2) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = (∑ i, ∑ j, (X i j) ^ 2) * (∑ j, (x j) ^ 2) := by rw [← Finset.sum_mul]
  -- frobeniusNorm X ^ 2 = ∑ i ∑ j Xij²
  have hfrob2 : frobeniusNorm X ^ 2 = ∑ i, ∑ j, (X i j) ^ 2 := by
    unfold frobeniusNorm frobeniusNormSq
    rw [Real.sq_sqrt (by positivity)]
  -- combine
  have hkey : ‖(toEuclideanLin X) x‖ ^ 2 ≤ (frobeniusNorm X * ‖x‖) ^ 2 := by
    rw [hlhs2, mul_pow, hfrob2, hx2]; exact hsum
  have h1 := norm_nonneg ((toEuclideanLin X) x)
  have h2 : 0 ≤ frobeniusNorm X * ‖x‖ := by
    apply mul_nonneg; · unfold frobeniusNorm; exact Real.sqrt_nonneg _
    · exact norm_nonneg _
  nlinarith [hkey, h1, h2]

/-- spectralNorm X ≤ frobeniusNorm X. -/
theorem spectralNorm_le_frobeniusNorm (X : RealMatrix n1 n2) :
    spectralNorm X ≤ frobeniusNorm X := by
  unfold spectralNorm
  apply ContinuousLinearMap.opNorm_le_bound
  · unfold frobeniusNorm; exact Real.sqrt_nonneg _
  · intro x
    have h := toEuclideanLin_apply_le_frobenius X x
    simpa using h

theorem sum4_reorder {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  have hL : (∑ i, ∑ j, ∑ k, ∑ l, f i j k l)
      = ∑ p : α × β, ∑ q : γ × δ, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type' (fun (i : α) (j : β) => ∑ k, ∑ l, f i j k l)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Fintype.sum_prod_type' (fun (k : γ) (l : δ) => f p.1 p.2 k l)]
  have hR : (∑ k, ∑ l, ∑ i, ∑ j, f i j k l)
      = ∑ q : γ × δ, ∑ p : α × β, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type' (fun (k : γ) (l : δ) => ∑ i, ∑ j, f i j k l)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Fintype.sum_prod_type' (fun (i : α) (j : β) => f i j q.1 q.2)]
  rw [hL, hR, Finset.sum_comm]

/-- frobeniusNormSq (signMatrix S) = r  (UV^T is a rank-r partial isometry). -/
theorem frobeniusNormSq_signMatrix (S : SVD M r) :
    frobeniusNormSq (signMatrix S) = (r : ℝ) := by
  unfold frobeniusNormSq
  have hEij : ∀ i j, (signMatrix S) i j = ∑ k, S.u k i * S.v k j := by
    intro i j; unfold signMatrix
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hentry : ∀ i j, (signMatrix S) i j ^ 2
      = ∑ k, ∑ l, (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
    intro i j
    rw [hEij i j, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _; ring
  calc (∑ i, ∑ j, (signMatrix S) i j ^ 2)
      = ∑ i, ∑ j, ∑ k, ∑ l, (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hentry i j]
    _ = ∑ k, ∑ l, ∑ i, ∑ j, (S.u k i * S.u l i) * (S.v k j * S.v l j) :=
        sum4_reorder (fun i j k l => (S.u k i * S.u l i) * (S.v k j * S.v l j))
    _ = ∑ k, ∑ l, (∑ i, S.u k i * S.u l i) * (∑ j, S.v k j * S.v l j) := by
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        rw [Finset.sum_mul_sum]
    _ = ∑ k, ∑ l, (if k = l then (1:ℝ) else 0) * (if k = l then (1:ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        rw [S.u_orthonormal k l, S.v_orthonormal k l]
    _ = (r : ℝ) := by
        have hk : ∀ k : Fin r,
            (∑ l, (if k = l then (1:ℝ) else 0) * (if k = l then (1:ℝ) else 0)) = (1:ℝ) := by
          intro k
          rw [Finset.sum_eq_single k]
          · simp
          · intro l _ hl; rw [if_neg (fun h => hl h.symm)]; ring
          · intro h; exact absurd (Finset.mem_univ k) h
        rw [Finset.sum_congr rfl (fun k _ => hk k)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp

/-- frobeniusNorm (signMatrix S) = √r. -/
theorem frobeniusNorm_signMatrix (S : SVD M r) :
    frobeniusNorm (signMatrix S) = Real.sqrt (r : ℝ) := by
  unfold frobeniusNorm
  rw [frobeniusNormSq_signMatrix S]

-- =================== Scratch_c7 (spectralNorm_smul) ===================
theorem spectralNorm_smul {n1 n2 : Nat} (c : ℝ) (X : RealMatrix n1 n2) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [show (Matrix.toEuclideanLin (c • X))
        = c • (Matrix.toEuclideanLin X) from by
        ext v; simp [map_smul]]
  rw [show (LinearMap.toContinuousLinearMap (c • Matrix.toEuclideanLin X))
        = c • (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)) from by
        ext v; simp]
  rw [norm_smul]
  simp [Real.norm_eq_abs]

-- =================== Scratch_s29core ===================
theorem spectralNorm_zero' : spectralNorm (0 : RealMatrix n1 n2) = 0 := by
  unfold spectralNorm; simp

theorem spectralNorm_add_le' (A B : RealMatrix n1 n2) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  unfold spectralNorm
  rw [show toEuclideanLin (A + B) = toEuclideanLin A + toEuclideanLin B from map_add _ _ _]
  rw [show LinearMap.toContinuousLinearMap (toEuclideanLin A + toEuclideanLin B)
        = LinearMap.toContinuousLinearMap (toEuclideanLin A)
          + LinearMap.toContinuousLinearMap (toEuclideanLin B) from map_add _ _ _]
  exact norm_add_le _ _

theorem spectralNorm_sum_le' {ι : Type*} (s : Finset ι) (f : ι → RealMatrix n1 n2) :
    spectralNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, spectralNorm (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [spectralNorm_zero']
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (spectralNorm_add_le' _ _) (by linarith [ih])

/-- General-ε contraction of H on T:  given concentration at ε,  ‖H X‖ ≤ ε ‖X‖. -/
theorem neumannErrorOperator_contraction_eps
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p ε : ℝ) (hp : 0 < p)
    (hconc : TangentSamplingConcentration Omega S p ε)
    (X : RealMatrix n1 n2) (hX : tangentProjection S X = X) :
    frobeniusNorm (neumannErrorOperator Omega S p X) ≤ ε * frobeniusNorm X := by
  have hHX : neumannErrorOperator Omega S p X
      = (-p⁻¹) • (tangentProjection S (samplingProjection Omega X) - p • X) := by
    rw [neumannErrorOperator_of_mem Omega S p X hX, smul_sub, neg_smul, neg_smul, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hp), one_smul]; abel
  rw [hHX, frobeniusNorm_smul']
  have habs : |(-p⁻¹)| = p⁻¹ := by rw [abs_neg, abs_of_pos (inv_pos.mpr hp)]
  rw [habs]
  have hkey := hconc X hX
  have hpinv : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp)
  calc p⁻¹ * frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
      ≤ p⁻¹ * (ε * p * frobeniusNorm X) := mul_le_mul_of_nonneg_left hkey hpinv
    _ = ε * frobeniusNorm X := by
        rw [show p⁻¹ * (ε * p * frobeniusNorm X) = ε * (p⁻¹ * p) * frobeniusNorm X by ring,
          inv_mul_cancel₀ (ne_of_gt hp)]; ring

/-- General-ε geometric decay:  ‖H^[k] E‖ ≤ ε^k ‖E‖  (needs 0 ≤ ε). -/
theorem neumannIterate_geometric_eps
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε)
    (hconc : TangentSamplingConcentration Omega S p ε) (k : ℕ) :
    frobeniusNorm (neumannIterate Omega S p k) ≤ ε ^ k * frobeniusNorm (signMatrix S) := by
  induction k with
  | zero => simp only [neumannIterate, Function.iterate_zero_apply, pow_zero, one_mul]; exact le_refl _
  | succ k ih =>
      simp only [neumannIterate, Function.iterate_succ_apply']
      have hmem := neumannIterate_mem Omega S p k
      have hstep := neumannErrorOperator_contraction_eps Omega S p ε hp hconc
        (neumannIterate Omega S p k) hmem
      calc frobeniusNorm (neumannErrorOperator Omega S p (neumannIterate Omega S p k))
          ≤ ε * frobeniusNorm (neumannIterate Omega S p k) := hstep
        _ ≤ ε * (ε ^ k * frobeniusNorm (signMatrix S)) := mul_le_mul_of_nonneg_left ih hε
        _ = ε ^ (k + 1) * frobeniusNorm (signMatrix S) := by ring

/-! ## Sampling Frobenius bound (c756305c_pos content) -/

theorem matrixInner_comm' (X Y : RealMatrix n1 n2) :
    matrixInner X Y = matrixInner Y X := by
  unfold matrixInner; apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

theorem sampling_selfAdjoint' (Omega : Finset (Fin n1 × Fin n2))
    (X Y : RealMatrix n1 n2) :
    matrixInner X (samplingProjection Omega Y) = matrixInner (samplingProjection Omega X) Y := by
  unfold matrixInner samplingProjection
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  by_cases h : (i, j) ∈ Omega <;> simp [h]

theorem sampling_idem' (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    samplingProjection Omega (samplingProjection Omega X) = samplingProjection Omega X := by
  funext i j; unfold samplingProjection
  by_cases h : (i, j) ∈ Omega <;> simp [h]

theorem sampling_normSq_eq' (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    frobeniusNormSq (samplingProjection Omega X) = matrixInner X (samplingProjection Omega X) := by
  rw [← matrixInner_self, matrixInner_comm' (samplingProjection Omega X) (samplingProjection Omega X),
    ← sampling_selfAdjoint' Omega X (samplingProjection Omega X), sampling_idem']

/-- For X ∈ T under concentration at ε ≤ 1/2:  ‖P_Ω X‖_F ≤ √(3p/2) ‖X‖_F. -/
theorem sampling_frobenius_bound
    (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p epsilon : ℝ)
    (hp : 0 < p) (hε : epsilon ≤ (1 : ℝ) / 2)
    (hTSC : TangentSamplingConcentration Omega S p epsilon)
    (X : RealMatrix n1 n2) (hXT : tangentProjection S X = X) :
    frobeniusNorm (samplingProjection Omega X) ≤ Real.sqrt (((3 : ℝ) * p) / 2) * frobeniusNorm X := by
  set A := samplingProjection Omega X with hA
  have hnormSq : frobeniusNormSq A = matrixInner X A := sampling_normSq_eq' Omega X
  have hPT : matrixInner X A = matrixInner X (tangentProjection S A) := by
    have hsa := tangentProjection_selfAdjoint S X A
    rw [hsa, hXT]
  have hsplit : matrixInner X (tangentProjection S A)
      = matrixInner X (tangentProjection S A - p • X) + p * matrixInner X X := by
    unfold matrixInner
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    simp [Matrix.sub_apply, Matrix.smul_apply]; ring
  set D := tangentProjection S A - p • X with hD
  have hcs : matrixInner X D ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq D := matrixInner_sq_le X D
  have hDbound : frobeniusNorm D ≤ epsilon * p * frobeniusNorm X := by
    have := hTSC X hXT; simpa [hD, hA] using this
  have hXnn : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
  have hDnn : 0 ≤ frobeniusNorm D := Real.sqrt_nonneg _
  have hcross : matrixInner X D ≤ frobeniusNorm X * (epsilon * p * frobeniusNorm X) := by
    have hle : matrixInner X D ≤ frobeniusNorm X * frobeniusNorm D := by
      have h1 : matrixInner X D ^ 2 ≤ (frobeniusNorm X * frobeniusNorm D) ^ 2 := by
        rw [mul_pow, ← frobeniusNormSq_eq_sq, ← frobeniusNormSq_eq_sq]; exact hcs
      nlinarith [le_abs_self (matrixInner X D), sq_abs (matrixInner X D),
        mul_nonneg hXnn hDnn, h1, abs_nonneg (matrixInner X D)]
    calc matrixInner X D ≤ frobeniusNorm X * frobeniusNorm D := hle
      _ ≤ frobeniusNorm X * (epsilon * p * frobeniusNorm X) :=
          mul_le_mul_of_nonneg_left hDbound hXnn
  have hXX : matrixInner X X = frobeniusNorm X ^ 2 := by
    rw [matrixInner_self, frobeniusNormSq_eq_sq]
  have hAsq_eq : frobeniusNorm A ^ 2 = matrixInner X D + p * matrixInner X X := by
    rw [← frobeniusNormSq_eq_sq, hnormSq, hPT, hsplit]
  have hAsq_le : frobeniusNorm A ^ 2 ≤ (3/2) * p * frobeniusNorm X ^ 2 := by
    rw [hAsq_eq, hXX]
    have hεp : epsilon * p ≤ (1/2) * p := mul_le_mul_of_nonneg_right hε (le_of_lt hp)
    nlinarith [hcross, hXnn, hp.le, sq_nonneg (frobeniusNorm X), hεp,
      mul_nonneg (le_of_lt hp) (sq_nonneg (frobeniusNorm X))]
  have hbound_nn : 0 ≤ Real.sqrt ((3 * p) / 2) := Real.sqrt_nonneg _
  have hAnn : 0 ≤ frobeniusNorm A := Real.sqrt_nonneg _
  have hsqrhs : (Real.sqrt ((3 * p) / 2) * frobeniusNorm X) ^ 2
      = (3/2) * p * frobeniusNorm X ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hsq : frobeniusNorm A ^ 2 ≤ (Real.sqrt ((3 * p) / 2) * frobeniusNorm X) ^ 2 := by
    rw [hsqrhs]; exact hAsq_le
  nlinarith [hsq, hAnn, mul_nonneg hbound_nn hXnn,
    sq_nonneg (frobeniusNorm A - Real.sqrt ((3*p)/2) * frobeniusNorm X)]

/-! ## Per-term spectral bound for the certificate tail -/

/-- spectralNorm (certificate term k) ≤ p⁻¹ √(3p/2) ε^k √r. -/
theorem cert_term_spectral_bound
    (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p ε : ℝ)
    (hp : 0 < p) (hε0 : 0 ≤ ε) (hε : ε ≤ (1 : ℝ) / 2)
    (hTSC : TangentSamplingConcentration Omega S p ε) (k : ℕ) :
    spectralNorm (neumannCertificateTerm Omega S p k)
      ≤ p⁻¹ * (Real.sqrt (((3 : ℝ) * p) / 2) * (ε ^ k * frobeniusNorm (signMatrix S))) := by
  -- unfold the certificate term; the inner tangentProjection of the iterate is the identity
  have hmem := neumannIterate_mem Omega S p k
  have hterm : neumannCertificateTerm Omega S p k
      = p⁻¹ • normalProjection S (samplingProjection Omega (neumannIterate Omega S p k)) := by
    unfold neumannCertificateTerm; rw [hmem]
  rw [hterm, spectralNorm_smul]
  have hpinv_nn : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp)
  rw [abs_of_nonneg hpinv_nn]
  apply mul_le_mul_of_nonneg_left _ hpinv_nn
  -- spectralNorm (P_⊥ (P_Ω (H^k E))) ≤ frob (P_⊥ (P_Ω (H^k E))) ≤ frob (P_Ω (H^k E))
  calc spectralNorm (normalProjection S (samplingProjection Omega (neumannIterate Omega S p k)))
      ≤ frobeniusNorm (normalProjection S (samplingProjection Omega (neumannIterate Omega S p k))) :=
        spectralNorm_le_frobeniusNorm _
    _ ≤ frobeniusNorm (samplingProjection Omega (neumannIterate Omega S p k)) :=
        normalProjection_contraction S _
    _ ≤ Real.sqrt (((3:ℝ)*p)/2) * frobeniusNorm (neumannIterate Omega S p k) :=
        sampling_frobenius_bound S Omega p ε hp hε hTSC (neumannIterate Omega S p k) hmem
    _ ≤ Real.sqrt (((3:ℝ)*p)/2) * (ε ^ k * frobeniusNorm (signMatrix S)) := by
        apply mul_le_mul_of_nonneg_left
          (neumannIterate_geometric_eps Omega S p ε hp hε0 hTSC k)
          (Real.sqrt_nonneg _)

/-! ## Geometric tail sum -/

/-- For 0 ≤ ε ≤ 1/2 and K ≥ 3:  ∑_{k∈Icc 3 K} ε^k ≤ 2 ε³ − 2 ε^{K+1}. -/
theorem geom_tail_invariant (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ (1:ℝ)/2) (K : ℕ) (hK : 3 ≤ K) :
    (∑ k ∈ Finset.Icc 3 K, ε ^ k) ≤ 2 * ε ^ 3 - 2 * ε ^ (K + 1) := by
  induction K with
  | zero => omega
  | succ K ih =>
      rcases Nat.lt_or_ge K 3 with hlt | hge
      · -- K < 3 and 3 ≤ K+1 ⇒ K = 2, Icc 3 3 = {3}
        interval_cases K
        · omega
        · omega
        · -- K = 2, K+1 = 3
          simp only [Finset.Icc_self, Finset.sum_singleton]
          have h1 : ε ^ 3 ≤ 2 * ε ^ 3 - 2 * ε ^ 4 := by nlinarith [pow_nonneg hε0 3, hε, hε0]
          simpa using h1
      · -- 3 ≤ K
        rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ K + 1)]
        have ihK := ih hge
        -- ∑ + ε^{K+1} ≤ (2ε³ - 2ε^{K+1}) + ε^{K+1} = 2ε³ - ε^{K+1} ≤ 2ε³ - 2ε^{K+2}
        have hstep : (2 * ε ^ 3 - 2 * ε ^ (K + 1)) + ε ^ (K + 1) ≤ 2 * ε ^ 3 - 2 * ε ^ (K + 1 + 1) := by
          have hpk : 0 ≤ ε ^ (K + 1) := pow_nonneg hε0 _
          have hpow : ε ^ (K + 1 + 1) = ε * ε ^ (K + 1) := by ring
          rw [hpow]; nlinarith [hpk, hε, hε0]
        calc (∑ k ∈ Finset.Icc 3 K, ε ^ k) + ε ^ (K + 1)
            ≤ (2 * ε ^ 3 - 2 * ε ^ (K + 1)) + ε ^ (K + 1) := by linarith [ihK]
          _ ≤ 2 * ε ^ 3 - 2 * ε ^ (K + 1 + 1) := hstep

/-- Clean tail bound:  ∑_{k∈Icc 3 K} ε^k ≤ 2 ε³. -/
theorem geom_tail_le (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ (1:ℝ)/2) (K : ℕ) (hK : 3 ≤ K) :
    (∑ k ∈ Finset.Icc 3 K, ε ^ k) ≤ 2 * ε ^ 3 := by
  have h := geom_tail_invariant ε hε0 hε K hK
  have : 0 ≤ 2 * ε ^ (K + 1) := by positivity
  linarith

/-! ## Assembly: spectral bound on the certificate partial sum -/

/-- For K ≥ 3:  spectralNorm(∑_{Icc 3 K} term_k) ≤ p⁻¹ √(3p/2) √r · 2 ε³. -/
theorem cert_partialSum_spectral_le
    (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p ε : ℝ)
    (hp : 0 < p) (hε0 : 0 ≤ ε) (hε : ε ≤ (1 : ℝ) / 2)
    (hTSC : TangentSamplingConcentration Omega S p ε) (K : ℕ) (hK : 3 ≤ K) :
    spectralNorm (∑ k ∈ Finset.Icc 3 K, neumannCertificateTerm Omega S p k)
      ≤ p⁻¹ * (Real.sqrt (((3 : ℝ) * p) / 2) * frobeniusNorm (signMatrix S)) * (2 * ε ^ 3) := by
  set C0 : ℝ := p⁻¹ * (Real.sqrt (((3:ℝ)*p)/2) * frobeniusNorm (signMatrix S)) with hC0
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]; apply mul_nonneg (le_of_lt (inv_pos.mpr hp))
    apply mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- triangle
  calc spectralNorm (∑ k ∈ Finset.Icc 3 K, neumannCertificateTerm Omega S p k)
      ≤ ∑ k ∈ Finset.Icc 3 K, spectralNorm (neumannCertificateTerm Omega S p k) :=
        spectralNorm_sum_le' _ _
    _ ≤ ∑ k ∈ Finset.Icc 3 K, C0 * ε ^ k := by
        apply Finset.sum_le_sum; intro k _
        have h := cert_term_spectral_bound S Omega p ε hp hε0 hε hTSC k
        rw [hC0]
        calc spectralNorm (neumannCertificateTerm Omega S p k)
            ≤ p⁻¹ * (Real.sqrt (((3:ℝ)*p)/2) * (ε ^ k * frobeniusNorm (signMatrix S))) := h
          _ = p⁻¹ * (Real.sqrt (((3:ℝ)*p)/2) * frobeniusNorm (signMatrix S)) * ε ^ k := by ring
    _ = C0 * (∑ k ∈ Finset.Icc 3 K, ε ^ k) := by rw [Finset.mul_sum]
    _ ≤ C0 * (2 * ε ^ 3) := by
        apply mul_le_mul_of_nonneg_left (geom_tail_le ε hε0 hε K hK) hC0nn

-- =================== Scratch_s29formula ===================
theorem rpow_three_half' (D : ℝ) (hD : 0 ≤ D) :
    Real.rpow D ((3:ℝ)/2) = D * Real.sqrt D := by
  rcases eq_or_lt_of_le hD with hD0 | hDpos
  · rw [← hD0]; simp [Real.zero_rpow (by norm_num : ((3:ℝ)/2) ≠ 0)]
  · have h1 : Real.rpow D ((3:ℝ)/2) = Real.rpow D 1 * Real.rpow D ((1:ℝ)/2) := by
      have := Real.rpow_add hDpos 1 ((1:ℝ)/2)
      rw [show (1:ℝ) + (1:ℝ)/2 = (3:ℝ)/2 by ring] at this
      exact this
    rw [h1, show Real.rpow D ((1:ℝ)/2) = Real.sqrt D from (Real.sqrt_eq_rpow D).symm,
      show Real.rpow D 1 = D from Real.rpow_one D]

/-- ε³ = Cdev³ · rpow D (3/2)  where ε = Cdev·√D, D ≥ 0. -/
theorem eps_cube_eq' (Cdev D : ℝ) (hD : 0 ≤ D) :
    (Cdev * Real.sqrt D) ^ 3 = Cdev ^ 3 * Real.rpow D ((3:ℝ)/2) := by
  rw [rpow_three_half' D hD, mul_pow]
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
  have : Real.sqrt D ^ 3 = D * Real.sqrt D := by
    rw [show (3:ℕ) = 2 + 1 by rfl, pow_add, hsq, pow_one]
  rw [this]

/-- The key prefactor identity:  p⁻¹·√(3p/2)·√r = √(3/2)·√(r·n₁n₂/m)
when p = m/(n₁n₂), m>0, n₁n₂>0, r≥0. -/
theorem prefactor_eq (n₁ n₂ m : ℕ) (r : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hm : 0 < m) (hr : 0 ≤ r) :
    let p := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
    p⁻¹ * (Real.sqrt (((3:ℝ)*p)/2) * Real.sqrt r)
      = Real.sqrt ((3:ℝ)/2) * Real.sqrt (r * ((n₁:ℝ)*(n₂:ℝ)) / (m:ℝ)) := by
  intro p
  have hnn : (0:ℝ) < (n₁:ℝ) * (n₂:ℝ) := by positivity
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hppos : 0 < p := by simp only [p]; positivity
  -- √(3p/2) = √(3/2) * √p
  have hsplit : Real.sqrt (((3:ℝ)*p)/2) = Real.sqrt ((3:ℝ)/2) * Real.sqrt p := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ (3:ℝ)/2)]
    congr 1; ring
  rw [hsplit]
  -- p⁻¹ * (√(3/2) * √p * √r) = √(3/2) * (p⁻¹ * √p) * √r
  -- p⁻¹ * √p = √(1/p) = √(n₁n₂/m)
  have hpinv_sqrt : p⁻¹ * Real.sqrt p = Real.sqrt p⁻¹ := by
    rw [Real.sqrt_inv]
    field_simp
    rw [Real.sq_sqrt hppos.le]
  -- assemble
  have hpinv_val : p⁻¹ = ((n₁:ℝ)*(n₂:ℝ)) / (m:ℝ) := by
    simp only [p]; rw [inv_div]
  calc p⁻¹ * (Real.sqrt ((3:ℝ)/2) * Real.sqrt p * Real.sqrt r)
      = Real.sqrt ((3:ℝ)/2) * (p⁻¹ * Real.sqrt p) * Real.sqrt r := by ring
    _ = Real.sqrt ((3:ℝ)/2) * Real.sqrt p⁻¹ * Real.sqrt r := by rw [hpinv_sqrt]
    _ = Real.sqrt ((3:ℝ)/2) * (Real.sqrt p⁻¹ * Real.sqrt r) := by ring
    _ = Real.sqrt ((3:ℝ)/2) * Real.sqrt (p⁻¹ * r) := by
        rw [Real.sqrt_mul (by rw [hpinv_val]; positivity)]
    _ = Real.sqrt ((3:ℝ)/2) * Real.sqrt (r * ((n₁:ℝ)*(n₂:ℝ)) / (m:ℝ)) := by
        rw [hpinv_val]; congr 2; ring

/-- The final formula-matching scalar inequality. -/
theorem formula_match
    (Cdev β μ₀ : ℝ) (n₁ n₂ r m : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r) (hm : 0 < m) (hμ₀ : 1 ≤ μ₀) (hβ : 2 < β) :
    let n := max n₁ n₂
    let p := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
    let ε := tangentSamplingDeviationScale Cdev β μ₀ n r m
    p⁻¹ * (Real.sqrt (((3:ℝ)*p)/2) * Real.sqrt (r:ℝ)) * (2 * ε ^ 3)
      ≤ neumannRemainderFormulaBound (2 * Real.sqrt ((3:ℝ)/2) * |Cdev| ^ 3 + 1) β μ₀ n r m := by
  intro n p ε
  -- D = the inner radicand of ε and of rpow(·,3/2)
  set D : ℝ := (μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))) / (m : ℝ) with hDdef
  -- ε = Cdev * √D
  have hεeq : ε = Cdev * Real.sqrt D := by
    simp only [ε, tangentSamplingDeviationScale, hDdef]
  -- D ≥ 0 (needs log n ≥ 0; n = max n₁ n₂ ≥ 1; β > 2 > 0)
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by
    simp only [n]; have : 1 ≤ max n₁ n₂ := le_trans hn₁ (le_max_left _ _)
    exact_mod_cast this
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hμ₀nn : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hβnn : 0 ≤ β := by linarith
  have hrnn : (0:ℝ) ≤ (r:ℝ) := by positivity
  have hnnn : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hD_nn : 0 ≤ D := by
    rw [hDdef]; apply div_nonneg _ hmpos.le
    have : 0 ≤ β * Real.log (n:ℝ) := mul_nonneg hβnn hlog_nn
    positivity
  -- rewrite RHS
  show p⁻¹ * (Real.sqrt (((3:ℝ)*p)/2) * Real.sqrt (r:ℝ)) * (2 * ε ^ 3)
      ≤ neumannRemainderFormulaBound (2 * Real.sqrt ((3:ℝ)/2) * |Cdev| ^ 3 + 1) β μ₀ n r m
  -- ε³ = Cdev³ · rpow D (3/2)
  have hε3 : ε ^ 3 = Cdev ^ 3 * Real.rpow D ((3:ℝ)/2) := by
    rw [hεeq]; exact eps_cube_eq' Cdev D hD_nn
  -- prefactor identity
  have hpref := prefactor_eq n₁ n₂ m (r:ℝ) hn₁ hn₂ hm hrnn
  simp only at hpref
  -- LHS = 2 * Cdev³ * rpow D (3/2) * (√(3/2) * √(r n₁n₂/m))
  have hLHS : p⁻¹ * (Real.sqrt (((3:ℝ)*p)/2) * Real.sqrt (r:ℝ)) * (2 * ε ^ 3)
      = 2 * Cdev ^ 3 * Real.rpow D ((3:ℝ)/2)
        * (Real.sqrt ((3:ℝ)/2) * Real.sqrt ((r:ℝ) * ((n₁:ℝ)*(n₂:ℝ)) / (m:ℝ))) := by
    rw [hε3, hpref]; ring
  rw [hLHS]
  -- abbreviations
  set Rp := Real.rpow D ((3:ℝ)/2) with hRp
  have hRp_nn : 0 ≤ Rp := Real.rpow_nonneg hD_nn _
  set s32 := Real.sqrt ((3:ℝ)/2) with hs32
  have hs32_nn : 0 ≤ s32 := Real.sqrt_nonneg _
  -- √(r n₁n₂/m) ≤ √(n²r/m)
  have hsqrt_le : Real.sqrt ((r:ℝ) * ((n₁:ℝ)*(n₂:ℝ)) / (m:ℝ))
      ≤ Real.sqrt (((n:ℝ)^2 * (r:ℝ)) / (m:ℝ)) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff_of_pos_right hmpos]
    · -- r * (n₁ n₂) ≤ n² * r  since n₁ n₂ ≤ n²
      have hn12 : (n₁:ℝ) * (n₂:ℝ) ≤ (n:ℝ)^2 := by
        have hncast : (n:ℝ) = max (n₁:ℝ) (n₂:ℝ) := by simp only [n, Nat.cast_max]
        rw [hncast]
        have h1 : (n₁:ℝ) ≤ max (n₁:ℝ) (n₂:ℝ) := le_max_left _ _
        have h2 : (n₂:ℝ) ≤ max (n₁:ℝ) (n₂:ℝ) := le_max_right _ _
        have h1' : (0:ℝ) ≤ (n₁:ℝ) := by positivity
        have h2' : (0:ℝ) ≤ max (n₁:ℝ) (n₂:ℝ) := by positivity
        nlinarith [mul_le_mul h1 h2 (by positivity) h2']
      nlinarith [hn12, hrnn]
  -- assemble final bound
  unfold neumannRemainderFormulaBound
  -- RHS = (2 √(3/2) |Cdev|³ + 1) * √(n²r/m) * Rp
  set Sn := Real.sqrt (((n:ℝ)^2 * (r:ℝ)) / (m:ℝ)) with hSn
  have hSn_nn : 0 ≤ Sn := Real.sqrt_nonneg _
  -- LHS = 2 Cdev³ Rp s32 √(r n₁n₂/m) ≤ 2 |Cdev|³ Rp s32 Sn ≤ Ctail Sn Rp
  set T := Real.sqrt ((r:ℝ) * ((n₁:ℝ)*(n₂:ℝ)) / (m:ℝ)) with hT
  have hT_nn : 0 ≤ T := Real.sqrt_nonneg _
  have hCdev_cube : Cdev ^ 3 ≤ |Cdev| ^ 3 := by
    have h1 : |Cdev| ^ 3 = |Cdev ^ 3| := (abs_pow Cdev 3).symm
    rw [h1]; exact le_abs_self _
  -- step 1: 2 Cdev³ Rp s32 T ≤ 2 |Cdev|³ Rp s32 T
  have step1 : 2 * Cdev ^ 3 * Rp * (s32 * T) ≤ 2 * |Cdev| ^ 3 * Rp * (s32 * T) := by
    have hfac : 0 ≤ 2 * (Rp * (s32 * T)) := by positivity
    nlinarith [hCdev_cube, hRp_nn, hs32_nn, hT_nn, hfac]
  -- step 2: 2 |Cdev|³ Rp s32 T ≤ 2 |Cdev|³ Rp s32 Sn
  have step2 : 2 * |Cdev| ^ 3 * Rp * (s32 * T) ≤ 2 * |Cdev| ^ 3 * Rp * (s32 * Sn) := by
    have hfac : 0 ≤ 2 * |Cdev| ^ 3 * Rp * s32 := by positivity
    nlinarith [hsqrt_le, hfac, mul_le_mul_of_nonneg_left hsqrt_le hfac]
  -- step 3: 2 |Cdev|³ Rp s32 Sn ≤ Ctail Sn Rp
  have step3 : 2 * |Cdev| ^ 3 * Rp * (s32 * Sn)
      ≤ (2 * s32 * |Cdev| ^ 3 + 1) * Sn * Rp := by
    have hSnRp : 0 ≤ Sn * Rp := mul_nonneg hSn_nn hRp_nn
    nlinarith [hSnRp, hSn_nn, hRp_nn, mul_nonneg hSn_nn hRp_nn]
  calc 2 * Cdev ^ 3 * Rp * (s32 * T)
      ≤ 2 * |Cdev| ^ 3 * Rp * (s32 * T) := step1
    _ ≤ 2 * |Cdev| ^ 3 * Rp * (s32 * Sn) := step2
    _ ≤ (2 * s32 * |Cdev| ^ 3 + 1) * Sn * Rp := step3

-- =================== Scratch_s29main ===================
theorem eps_nonneg_of_conc
    (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p ε : ℝ) (hp : 0 < p) (hr : 0 < r)
    (hconc : TangentSamplingConcentration Omega S p ε) : 0 ≤ ε := by
  have hmem : tangentProjection S (signMatrix S) = signMatrix S := tangent_signMatrix S
  have h := hconc (signMatrix S) hmem
  have hnn : 0 ≤ frobeniusNorm (tangentProjection S (samplingProjection Omega (signMatrix S))
      - p • signMatrix S) := Real.sqrt_nonneg _
  have hEpos : 0 < frobeniusNorm (signMatrix S) := by
    rw [frobeniusNorm_signMatrix S]
    exact Real.sqrt_pos.mpr (by exact_mod_cast hr)
  have hge : 0 ≤ p * frobeniusNorm (signMatrix S) * ε := by
    have h2 : 0 ≤ ε * p * frobeniusNorm (signMatrix S) := le_trans hnn h
    nlinarith [h2]
  have hpEpos : 0 < p * frobeniusNorm (signMatrix S) := mul_pos hp hEpos
  exact nonneg_of_mul_nonneg_right hge hpEpos

/-- The fe401eed target, proved as `solution` shape locally (n₁ n₂ explicit). -/
theorem solution_local
    (Cdev : ℝ) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r)
        (Omega : Finset (Fin n₁ × Fin n₂)),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m ≤ (1 : ℝ) / 2 →
        TangentSamplingConcentration Omega S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m) →
        NeumannCertificateTailSpectralBound Omega S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 3
          (neumannRemainderFormulaBound Ctail β μ₀ (max n₁ n₂) r m) := by
  refine ⟨2 * Real.sqrt ((3:ℝ)/2) * |Cdev| ^ 3 + 1, by positivity, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S Omega hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hεhalf hconc
  -- abbreviations
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  set ε : ℝ := tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m with hε_def
  -- m > 0 from concentration providing a meaningful bound? We need m > 0 for p > 0.
  -- Derive m > 0: if m = 0 then p = 0, and the certificate term has p⁻¹ = 0, term = 0.
  -- Cleanest: prove m > 0. Since ε ≤ 1/2 always holds; but p>0 needs m>0.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0 ⇒ p = 0 ⇒ p⁻¹ = 0 ⇒ each cert term = 0 ⇒ partial sums = 0 ≤ bound (bound ≥ 0)
    subst hm0
    intro K hK
    have hp0 : p = 0 := by simp [hp_def]
    -- every neumannCertificateTerm has factor p⁻¹ = 0
    have hterm0 : ∀ k, neumannCertificateTerm Omega S p k = 0 := by
      intro k; unfold neumannCertificateTerm
      rw [hp0]; simp
    have hsum0 : (∑ k ∈ Finset.Icc 3 K, neumannCertificateTerm Omega S p k) = 0 := by
      apply Finset.sum_eq_zero; intro k _; exact hterm0 k
    rw [hsum0, spectralNorm_zero']
    -- bound ≥ 0: m = 0 ⇒ radicands divide by 0 = 0
    unfold neumannRemainderFormulaBound
    have hcast0 : ((0:ℕ):ℝ) = (0:ℝ) := by norm_num
    rw [hcast0, div_zero, Real.sqrt_zero, mul_zero, zero_mul]
  · -- m > 0: main case
    have hppos : 0 < p := by rw [hp_def]; positivity
    have hε0 : 0 ≤ ε := eps_nonneg_of_conc S Omega p ε hppos hr hconc
    -- NeumannCertificateTailSpectralBound: ∀ K ≥ 3, ...
    intro K hK
    -- spectral chain
    have hchain := cert_partialSum_spectral_le S Omega p ε hppos hε0 hεhalf hconc K hK
    -- ‖E‖ = √r
    rw [frobeniusNorm_signMatrix S] at hchain
    -- formula match
    have hfm := formula_match Cdev β μ₀ n₁ n₂ r m hn₁ hn₂ hr hmpos hμ₀ hβ
    simp only at hfm
    -- chain: spectral ≤ p⁻¹·(√(3p/2)·√r)·(2ε³) ≤ formula bound
    calc spectralNorm (∑ k ∈ Finset.Icc 3 K, neumannCertificateTerm Omega S p k)
        ≤ p⁻¹ * (Real.sqrt (((3:ℝ)*p)/2) * Real.sqrt (r:ℝ)) * (2 * ε ^ 3) := hchain
      _ ≤ neumannRemainderFormulaBound (2 * Real.sqrt ((3:ℝ)/2) * |Cdev| ^ 3 + 1)
            β μ₀ (max n₁ n₂) r m := hfm


end MatrixCompletion

open MatrixCompletion

theorem solution (Cdev : ℝ) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
          ∀ (β : ℝ), 2 < β →
          ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
            (μ₀ μ₁ : ℝ) (S : SVD M r)
            (Omega : Finset (Fin n₁ × Fin n₂)),
            0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
            1 ≤ μ₀ → 1 ≤ μ₁ →
            A0 S μ₀ → A1 S μ₁ →
            tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m ≤ (1 : ℝ) / 2 →
            TangentSamplingConcentration Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m) →
            NeumannCertificateTailSpectralBound Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 3
              (neumannRemainderFormulaBound Ctail β μ₀ (max n₁ n₂) r m) :=
  MatrixCompletion.solution_local Cdev
