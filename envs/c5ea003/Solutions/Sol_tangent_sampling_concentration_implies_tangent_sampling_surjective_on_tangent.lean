-- Prove2me | solution 1 for tangent_sampling_concentration_implies_tangent_sampling_surjective_on_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T05:56:59.398705+00:00
-- url     : https://prove2.me/submissions/5da36cc8-ad19-47ce-9bc4-b57185f7e3e7

import Definitions.Def_matrix_completion_tangent
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Equiv

namespace MatrixCompletion

open scoped Classical BigOperators

/- ============ inlined Scratch_contraction ============ -/


-- ===== bring in the proven pieces (copied) =====

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

/-- The tangent projection is a Frobenius contraction. -/
theorem tangentProjection_contraction {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) :
    frobeniusNormSq (tangentProjection S X) ≤ frobeniusNormSq X := by
  set Y := tangentProjection S X with hY
  -- ‖Y‖² = ⟨Y,Y⟩ = ⟨X, P_T(P_T X)⟩ = ⟨X, Y⟩
  have hself : matrixInner Y Y = matrixInner X Y := by
    -- selfAdjoint: ⟨X, P_T Y⟩ = ⟨P_T X, Y⟩.  With Y = P_T X, P_T Y = P_T(P_T X) = P_T X = Y.
    have hsa := tangentProjection_selfAdjoint S X Y
    rw [hY] at hsa
    rw [tangent_idem] at hsa
    -- hsa : matrixInner X (tangentProjection S X) = matrixInner (tangentProjection S X) (tangentProjection S X)
    rw [hY]
    exact hsa.symm
  have hYY : frobeniusNormSq Y = matrixInner X Y := by
    rw [← matrixInner_self Y, hself]
  -- ⟨X,Y⟩ ≤ ‖X‖‖Y‖ ; so ‖Y‖² ≤ ‖X‖‖Y‖
  have hcs : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y :=
    matrixInner_sq_le X Y
  have hYYnn : 0 ≤ frobeniusNormSq Y := frobeniusNormSq_nonneg Y
  have hXXnn : 0 ≤ frobeniusNormSq X := frobeniusNormSq_nonneg X
  -- from hYY: frobeniusNormSq Y = matrixInner X Y, so (frobeniusNormSq Y)^2 = (matrixInner X Y)^2 ≤ ‖X‖²‖Y‖²
  have hsq : (frobeniusNormSq Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    calc (frobeniusNormSq Y) ^ 2 = (matrixInner X Y) ^ 2 := by rw [hYY]
      _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hcs
  -- conclude frobeniusNormSq Y ≤ frobeniusNormSq X
  rcases eq_or_lt_of_le hYYnn with h0 | hpos
  · rw [← h0]; exact hXXnn
  · -- divide hsq by frobeniusNormSq Y > 0
    have : frobeniusNormSq Y * frobeniusNormSq Y ≤ frobeniusNormSq X * frobeniusNormSq Y := by
      calc frobeniusNormSq Y * frobeniusNormSq Y = (frobeniusNormSq Y) ^ 2 := by ring
        _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hsq
    exact le_of_mul_le_mul_right this hpos

/-- The Parseval contraction: ∑ ⟨X, P_T e_ij⟩² ≤ ‖X‖²_F. -/
theorem tangent_projection_coordinate_parseval_contraction
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    (∑ i : Fin n1, ∑ j : Fin n2,
      matrixInner X (tangentProjection S (coordinateMatrix i j)) ^ 2)
      ≤ frobeniusNormSq X := by
  -- rewrite each term: ⟨X, P_T e_ij⟩ = ⟨P_T X, e_ij⟩ = (P_T X) i j
  have hterm : ∀ i : Fin n1, ∀ j : Fin n2,
      matrixInner X (tangentProjection S (coordinateMatrix i j))
        = tangentProjection S X i j := by
    intro i j
    rw [tangentProjection_selfAdjoint S X (coordinateMatrix i j)]
    rw [matrixInner_coordinateMatrix]
  have hrw : (∑ i : Fin n1, ∑ j : Fin n2,
      matrixInner X (tangentProjection S (coordinateMatrix i j)) ^ 2)
      = ∑ i : Fin n1, ∑ j : Fin n2, tangentProjection S X i j ^ 2 := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hterm i j]
  rw [hrw]
  -- this is frobeniusNormSq (P_T X)
  have heq : (∑ i : Fin n1, ∑ j : Fin n2, tangentProjection S X i j ^ 2)
      = frobeniusNormSq (tangentProjection S X) := rfl
  rw [heq]
  exact tangentProjection_contraction S X

/- ============ inlined Scratch_invert ============ -/



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
noncomputable def PT (S : SVD M r) : RealMatrix n1 n2 →ₗ[ℝ] RealMatrix n1 n2 :=
  IsLinearMap.mk' (tangentProjection S) ⟨tangent_add S, tangent_smul S⟩

@[simp] theorem PT_apply (S : SVD M r) (X : RealMatrix n1 n2) :
    PT S X = tangentProjection S X := rfl

/-! ## P_Ω linearity + self-adjointness -/

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

/- ============ inlined Scratch_invert2 ============ -/



variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- The tangent subspace T as the range of P_T. -/
noncomputable def Tsub (S : SVD M r) : Submodule ℝ (RealMatrix n1 n2) :=
  LinearMap.range (PT S)

theorem mem_Tsub_iff (S : SVD M r) (X : RealMatrix n1 n2) :
    X ∈ Tsub S ↔ tangentProjection S X = X := by
  constructor
  · rintro ⟨Y, hY⟩
    -- hY : PT S Y = X, i.e. tangentProjection S Y = X
    rw [PT_apply] at hY
    -- P_T X = P_T (P_T Y) = P_T Y = X
    calc tangentProjection S X = tangentProjection S (tangentProjection S Y) := by rw [hY]
      _ = tangentProjection S Y := tangent_idem S Y
      _ = X := hY
  · intro h
    exact ⟨X, by rw [PT_apply]; exact h⟩

/-- The least-squares operator B X = P_T (P_Ω (P_T X)). -/
noncomputable def Bop (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) :
    RealMatrix n1 n2 →ₗ[ℝ] RealMatrix n1 n2 :=
  (PT S).comp ((IsLinearMap.mk' (samplingProjection Omega)
      ⟨sampling_add Omega, sampling_smul Omega⟩).comp (PT S))

theorem Bop_apply (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (X : RealMatrix n1 n2) :
    Bop Omega S X
      = tangentProjection S (samplingProjection Omega (tangentProjection S X)) := rfl

/-- B always lands in T. -/
theorem Bop_mem_Tsub (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (X : RealMatrix n1 n2) :
    Bop Omega S X ∈ Tsub S := by
  rw [mem_Tsub_iff, Bop_apply, tangent_idem]

/-- B maps T into T. -/
theorem Bop_mapsTo (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) :
    ∀ X ∈ Tsub S, Bop Omega S X ∈ Tsub S :=
  fun X _ => Bop_mem_Tsub Omega S X

/-- Restriction of B to the endomorphism T → T. -/
noncomputable def BopT (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) :
    Tsub S →ₗ[ℝ] Tsub S :=
  (Bop Omega S).restrict (Bop_mapsTo Omega S)

/-- For X ∈ T, B X = P_T (P_Ω X) (the inner P_T is identity on T). -/
theorem Bop_apply_of_mem (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (X : RealMatrix n1 n2) (hX : tangentProjection S X = X) :
    Bop Omega S X = tangentProjection S (samplingProjection Omega X) := by
  rw [Bop_apply, hX]

/-! ## Injectivity of B on T from concentration + 0 < p -/

theorem BopT_injective (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : ℝ)
    (hp : 0 < p) (hconc : TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) :
    Function.Injective (BopT Omega S) := by
  rw [← LinearMap.ker_eq_bot]
  rw [LinearMap.ker_eq_bot']
  intro W hW
  -- W : Tsub S, BopT W = 0
  obtain ⟨W, hWmem⟩ := W
  rw [mem_Tsub_iff] at hWmem
  -- hW says the restricted map sends ⟨W,_⟩ to 0
  have hBW : Bop Omega S W = 0 := by
    have := congrArg (Subtype.val) hW
    simpa [BopT, LinearMap.restrict_coe_apply] using this
  -- B W = P_T (P_Ω W) = 0 since W ∈ T
  rw [Bop_apply_of_mem Omega S W hWmem] at hBW
  -- concentration: ‖P_T(P_Ω W) - p•W‖ ≤ (1/2) p ‖W‖
  have hkey := hconc W hWmem
  rw [hBW] at hkey
  -- now ‖0 - p•W‖ ≤ (1/2) p ‖W‖
  have hsub : (0 : RealMatrix n1 n2) - p • W = (-p) • W := by
    rw [zero_sub, neg_smul]
  rw [hsub, frobeniusNorm_smul'] at hkey
  have habs : |(-p)| = p := by rw [abs_neg, abs_of_pos hp]
  rw [habs] at hkey
  -- hkey : p * frobeniusNorm W ≤ (1/2) * p * frobeniusNorm W
  have hnormnn : 0 ≤ frobeniusNorm W := Real.sqrt_nonneg _
  have hnorm0 : frobeniusNorm W = 0 := by
    by_contra hne
    have hpos : 0 < frobeniusNorm W := lt_of_le_of_ne hnormnn (Ne.symm hne)
    nlinarith [hkey, hp, hpos]
  have hsq : frobeniusNormSq W = 0 := by
    have hnn : 0 ≤ frobeniusNormSq W := frobeniusNormSq_nonneg W
    have heq : frobeniusNormSq W = frobeniusNorm W ^ 2 := frobeniusNormSq_eq_sq W
    rw [heq, hnorm0]; ring
  have hW0 : W = 0 := (frobeniusNormSq_eq_zero_iff' W).1 hsq
  -- conclude the subtype is 0
  apply Subtype.ext
  simpa using hW0

/-! ## Surjectivity ⟹ existence of W ∈ T with B W = E -/

/-- From injectivity of the finite-dim endomorphism BopT, get a preimage of any
element of T.  Specialized to E = signMatrix S ∈ T. -/
theorem exists_preimage_signMatrix (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : ℝ) (hp : 0 < p) (hconc : TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) :
    ∃ W : RealMatrix n1 n2, tangentProjection S W = W ∧
      tangentProjection S (samplingProjection Omega W) = signMatrix S := by
  have hinj := BopT_injective Omega S p hp hconc
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  -- E ∈ T
  have hEmem : signMatrix S ∈ Tsub S := by
    rw [mem_Tsub_iff]; exact tangent_signMatrix S
  obtain ⟨W, hW⟩ := hsurj ⟨signMatrix S, hEmem⟩
  obtain ⟨W, hWmem⟩ := W
  rw [mem_Tsub_iff] at hWmem
  refine ⟨W, hWmem, ?_⟩
  -- BopT ⟨W,_⟩ = ⟨E, _⟩, take .val: Bop Omega S W = signMatrix S
  have hval := congrArg Subtype.val hW
  simp only [BopT, LinearMap.restrict_coe_apply] at hval
  -- hval : Bop Omega S W = signMatrix S
  rw [Bop_apply_of_mem Omega S W hWmem] at hval
  exact hval

/-! ## Minimality of Y = P_Ω W -/

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

/-- Frobenius norm-squared expansion: ‖Z‖² = ‖Y‖² + 2⟨Y, Z−Y⟩ + ‖Z−Y‖². -/
theorem frobeniusNormSq_expand (Y Z : RealMatrix n1 n2) :
    frobeniusNormSq Z
      = frobeniusNormSq Y + 2 * matrixInner Y (Z - Y) + frobeniusNormSq (Z - Y) := by
  unfold frobeniusNormSq matrixInner
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Matrix.sub_apply]; ring

/-- The orthogonality identity ⟨Y, Z−Y⟩ = 0 for the certificate. -/
theorem certificate_orthogonality (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (W Z : RealMatrix n1 n2)
    (hWmem : tangentProjection S W = W)
    (hZvan : VanishesOutside Omega Z)
    (hPTZ : tangentProjection S Z = signMatrix S)
    (hPTY : tangentProjection S (samplingProjection Omega W) = signMatrix S) :
    matrixInner (samplingProjection Omega W) (Z - samplingProjection Omega W) = 0 := by
  set Y := samplingProjection Omega W with hYdef
  -- Z - Y vanishes outside Ω
  have hYvan : VanishesOutside Omega Y := by
    intro i j hij; rw [hYdef]; unfold samplingProjection; simp [hij]
  have hDvan : VanishesOutside Omega (Z - Y) := by
    intro i j hij
    simp only [Matrix.sub_apply, hZvan i j hij, hYvan i j hij, sub_zero]
  -- ⟨Y, Z−Y⟩ = ⟨P_Ω W, Z−Y⟩ = ⟨W, P_Ω (Z−Y)⟩ = ⟨W, Z−Y⟩
  have step1 : matrixInner Y (Z - Y) = matrixInner W (samplingProjection Omega (Z - Y)) := by
    rw [hYdef]
    rw [← sampling_selfAdjoint Omega W (Z - samplingProjection Omega W)]
  rw [step1]
  rw [sampling_of_vanishesOutside Omega (Z - Y) hDvan]
  -- ⟨W, Z−Y⟩ = ⟨P_T W, Z−Y⟩ = ⟨W, P_T(Z−Y)⟩
  have step2 : matrixInner W (Z - Y)
      = matrixInner (tangentProjection S W) (Z - Y) := by rw [hWmem]
  rw [step2, ← tangentProjection_selfAdjoint S W (Z - Y)]
  -- P_T (Z - Y) = P_T Z - P_T Y = E - E = 0
  have hPTsub : tangentProjection S (Z - Y) = 0 := by
    rw [tangent_sub, hPTZ, hYdef, hPTY, sub_self]
  rw [hPTsub, matrixInner_zero_right]

/-- The minimality property of Y = P_Ω W. -/
theorem certificate_minimal (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (W Z : RealMatrix n1 n2)
    (hWmem : tangentProjection S W = W)
    (hZvan : VanishesOutside Omega Z)
    (hPTZ : tangentProjection S Z = signMatrix S)
    (hPTY : tangentProjection S (samplingProjection Omega W) = signMatrix S) :
    frobeniusNormSq (samplingProjection Omega W) ≤ frobeniusNormSq Z := by
  set Y := samplingProjection Omega W with hYdef
  have hortho := certificate_orthogonality Omega S W Z hWmem hZvan hPTZ hPTY
  rw [← hYdef] at hortho
  have hexp := frobeniusNormSq_expand Y Z
  rw [hortho] at hexp
  have hDnn : 0 ≤ frobeniusNormSq (Z - Y) := frobeniusNormSq_nonneg (Z - Y)
  rw [hexp]; nlinarith [hDnn]

/-! ## Final assembly: certificate exists -/

theorem certificate_exists (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p : ℝ) (hp : 0 < p) (hconc : TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) :
    ∃ Y : RealMatrix n1 n2, LeastSquaresDualCertificate Omega S Y := by
  obtain ⟨W, hWmem, hBW⟩ := exists_preimage_signMatrix Omega S p hp hconc
  refine ⟨samplingProjection Omega W, ?_, ?_, ?_⟩
  · -- VanishesOutside
    intro i j hij; unfold samplingProjection; simp [hij]
  · -- P_T Y = signMatrix S
    exact hBW
  · -- minimality
    intro Z hZvan hPTZ
    exact certificate_minimal Omega S W Z hWmem hZvan hPTZ hBW



/- ============ surjectivity ============ -/
variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

theorem tangent_sampling_surjective_of_concentration
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) (p : ℝ)
    (hp : 0 < p) (hconc : TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) :
    TangentSamplingOperatorSurjectiveOnT Omega S := by
  have hinj := BopT_injective Omega S p hp hconc
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro X hXmem
  have hXT : X ∈ Tsub S := by rw [mem_Tsub_iff]; exact hXmem
  obtain ⟨W, hW⟩ := hsurj ⟨X, hXT⟩
  obtain ⟨W, hWmem⟩ := W
  rw [mem_Tsub_iff] at hWmem
  refine ⟨W, hWmem, ?_⟩
  have hval := congrArg Subtype.val hW
  simp only [BopT, LinearMap.restrict_coe_apply] at hval
  rw [Bop_apply_of_mem Omega S W hWmem] at hval
  exact hval

end MatrixCompletion

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 < p →
    TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
    TangentSamplingOperatorSurjectiveOnT Omega S := by
  intro hp hconc
  exact MatrixCompletion.tangent_sampling_surjective_of_concentration Omega S p hp hconc
