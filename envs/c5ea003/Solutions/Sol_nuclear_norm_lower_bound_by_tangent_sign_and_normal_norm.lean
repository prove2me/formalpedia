-- Prove2me | solution 1 for nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T20:13:57.695986+00:00
-- url     : https://prove2.me/submissions/b27ec9a8-7f88-4987-90f2-23c92d1e6927

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Theorems.Thm_matrix_trace_duality_inequality
import Theorems.Thm_sign_matrix_inner_eq_nuclear_norm
import Theorems.Thm_normal_space_dual_achiever_with_sign_contraction

/-!
Reduction of node 40a58360 `nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm`
to the trace-duality cores:
  C1 = matrix_trace_duality_inequality   (⟨A,B⟩ ≤ ‖A‖_op ‖B‖_*)
  L1 = sign_matrix_inner_eq_nuclear_norm (⟨E,M⟩ = ‖M‖_*)
  L2 = normal_space_dual_achiever_with_sign_contraction
       (∃ W∈T⊥, ‖E+W‖_op≤1, ⟨W,N_H⟩=‖N_H‖_*).
CR2009 Lemma 3.2 / subgradient characterization (3.4), p.15.
The proved helpers (P_T algebra, M∈T) are inlined; only the three deep cores are imported.
-/

open scoped Classical BigOperators

namespace MatrixCompletion

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

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

theorem matrixInner_add_left (A B X : RealMatrix n1 n2) :
    matrixInner (A + B) X = matrixInner A X + matrixInner B X := by
  unfold matrixInner
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

/-- matrixInner additive in the right argument. -/

theorem matrixInner_add_right (X A B : RealMatrix n1 n2) :
    matrixInner X (A + B) = matrixInner X A + matrixInner X B := by
  unfold matrixInner
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

/-- matrixInner sub in left argument. -/

theorem matrixInner_sub_left (A B X : RealMatrix n1 n2) :
    matrixInner (A - B) X = matrixInner A X - matrixInner B X := by
  unfold matrixInner
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

theorem matrixInner_comm' (X Y : RealMatrix n1 n2) :
    matrixInner X Y = matrixInner Y X := by
  unfold matrixInner
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- F1: nuclear norm is nonnegative. -/

theorem nuclearNorm_nonneg (X : RealMatrix n1 n2) : 0 ≤ nuclearNorm X := by
  unfold nuclearNorm
  apply Finset.sum_nonneg
  intro i _
  exact (Matrix.toEuclideanLin X).singularValues_nonneg i

/-- F2: nuclear norm is zero iff the matrix is zero. -/

theorem nuclearNorm_eq_zero_iff (X : RealMatrix n1 n2) :
    nuclearNorm X = 0 ↔ X = 0 := by
  unfold nuclearNorm
  constructor
  · intro h
    -- sum of nonneg = 0 ⇒ all terms zero ⇒ singularValues = 0 ⇒ map = 0 ⇒ X = 0
    have hzero : (Matrix.toEuclideanLin X).singularValues = 0 := by
      ext i
      have hsupp := (Matrix.toEuclideanLin X).singularValues.support
      by_contra hne
      have hpos : 0 < (Matrix.toEuclideanLin X).singularValues i := by
        rcases lt_or_eq_of_le ((Matrix.toEuclideanLin X).singularValues_nonneg i) with h' | h'
        · exact h'
        · exact absurd h'.symm hne
      have : (Matrix.toEuclideanLin X).singularValues i ≤
          (Matrix.toEuclideanLin X).singularValues.sum (fun _ x => x) := by
        rw [Finsupp.sum]
        by_cases hi : i ∈ (Matrix.toEuclideanLin X).singularValues.support
        · exact Finset.single_le_sum
            (fun j _ => (Matrix.toEuclideanLin X).singularValues_nonneg j) hi
        · simp only [Finsupp.mem_support_iff, not_not] at hi
          rw [hi] at hpos; exact absurd hpos (lt_irrefl 0)
      rw [h] at this
      exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl 0)
    have : Matrix.toEuclideanLin X = 0 :=
      (LinearMap.singularValues_eq_zero_iff (T := Matrix.toEuclideanLin X)).mp hzero
    have hX : Matrix.toEuclideanLin X = Matrix.toEuclideanLin 0 := by rw [this]; simp
    exact (Matrix.toEuclideanLin).injective hX
  · intro h; subst h
    simp [LinearMap.singularValues_zero]

theorem left_rank1 (S : SVD M r) (k : Fin r) :
    leftSingularProjection S (Matrix.vecMulVec (S.u k) (S.v k))
      = Matrix.vecMulVec (S.u k) (S.v k) := by
  funext i j
  unfold leftSingularProjection
  simp only [Matrix.vecMulVec_apply]
  -- ∑ a (∑ l u_l i u_l a) (u_k a v_k j) = u_k i v_k j
  have e1 : (∑ a : Fin n1, (∑ l : Fin r, S.u l i * S.u l a) * (S.u k a * S.v k j))
      = ∑ l : Fin r, (S.u l i * S.v k j) * (∑ a : Fin n1, S.u l a * S.u k a) := by
    have step : (∑ a : Fin n1, (∑ l : Fin r, S.u l i * S.u l a) * (S.u k a * S.v k j))
        = ∑ a : Fin n1, ∑ l : Fin r, (S.u l i * S.v k j) * (S.u l a * S.u k a) := by
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
    rw [step, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]
  rw [e1]
  have e2 : (∑ l : Fin r, (S.u l i * S.v k j) * (∑ a : Fin n1, S.u l a * S.u k a))
      = ∑ l : Fin r, (if l = k then S.u l i * S.v k j else 0) := by
    apply Finset.sum_congr rfl; intro l _
    rw [S.u_orthonormal l k]; by_cases h : l = k <;> simp [h]
  rw [e2, Finset.sum_ite_eq']; simp

theorem right_rank1 (S : SVD M r) (k : Fin r) :
    rightSingularProjection S (Matrix.vecMulVec (S.u k) (S.v k))
      = Matrix.vecMulVec (S.u k) (S.v k) := by
  funext i j
  unfold rightSingularProjection
  simp only [Matrix.vecMulVec_apply]
  have e1 : (∑ b : Fin n2, (S.u k i * S.v k b) * (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n2, S.v k b * S.v l b) := by
    have step : (∑ b : Fin n2, (S.u k i * S.v k b) * (∑ l : Fin r, S.v l b * S.v l j))
        = ∑ b : Fin n2, ∑ l : Fin r, (S.u k i * S.v l j) * (S.v k b * S.v l b) := by
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
    rw [step, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]
  rw [e1]
  have e2 : (∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n2, S.v k b * S.v l b))
      = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
    apply Finset.sum_congr rfl; intro l _
    rw [S.v_orthonormal k l]; by_cases h : k = l <;> simp [h]
  rw [e2, Finset.sum_ite_eq]; simp

theorem two_rank1 (S : SVD M r) (k : Fin r) :
    twoSidedSingularProjection S (Matrix.vecMulVec (S.u k) (S.v k))
      = Matrix.vecMulVec (S.u k) (S.v k) := by
  rw [two_eq_left_right, right_rank1, left_rank1]

theorem tangent_rank1 (S : SVD M r) (k : Fin r) :
    tangentProjection S (Matrix.vecMulVec (S.u k) (S.v k))
      = Matrix.vecMulVec (S.u k) (S.v k) := by
  unfold tangentProjection
  rw [left_rank1, right_rank1, two_rank1]; abel

/-- `tangentProjection` commutes with finite sums (it is linear). -/

theorem tangent_sum (S : SVD M r) {ι : Type*} (s : Finset ι)
    (f : ι → RealMatrix n1 n2) :
    tangentProjection S (∑ i ∈ s, f i) = ∑ i ∈ s, tangentProjection S (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      -- P_T 0 = 0
      have : tangentProjection S (0 : RealMatrix n1 n2) = 0 := by
        have := tangent_smul S 0 (0 : RealMatrix n1 n2)
        simpa using this
      exact this
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, tangent_add, ih]

theorem tangent_M (S : SVD M r) : tangentProjection S M = M := by
  have harg : tangentProjection S M
      = tangentProjection S (∑ k, S.sigma k • Matrix.vecMulVec (S.u k) (S.v k)) :=
    congrArg (tangentProjection S) S.decomp
  rw [harg, tangent_sum]
  have hsum : (∑ k, tangentProjection S (S.sigma k • Matrix.vecMulVec (S.u k) (S.v k)))
      = ∑ k, S.sigma k • Matrix.vecMulVec (S.u k) (S.v k) := by
    apply Finset.sum_congr rfl; intro k _
    rw [tangent_smul, tangent_rank1 S k]
  rw [hsum, ← S.decomp]

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

end MatrixCompletion

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    nuclearNorm M +
        matrixInner (signMatrix S) (tangentProjection S H) +
          nuclearNorm (normalProjection S H) ≤
      nuclearNorm (M + H) := by
  set E := signMatrix S with hE
  obtain ⟨W, hWT, hEWnorm, hWNH⟩ := normal_space_dual_achiever_with_sign_contraction S H
  have hC1 := matrix_trace_duality_inequality (E + W) (M + H)
  have hMHnn : 0 ≤ nuclearNorm (M + H) := by
    unfold nuclearNorm
    apply Finset.sum_nonneg
    intro i _
    exact (Matrix.toEuclideanLin (M + H)).singularValues_nonneg i
  have hub : matrixInner (E + W) (M + H) ≤ nuclearNorm (M + H) := by
    calc matrixInner (E + W) (M + H)
        ≤ spectralNorm (E + W) * nuclearNorm (M + H) := hC1
      _ ≤ 1 * nuclearNorm (M + H) := by
            apply mul_le_mul_of_nonneg_right hEWnorm hMHnn
      _ = nuclearNorm (M + H) := one_mul _
  have hexp : matrixInner (E + W) (M + H)
      = matrixInner E M + matrixInner E H + matrixInner W M + matrixInner W H := by
    rw [matrixInner_add_left, matrixInner_add_right, matrixInner_add_right]; ring
  have hEM : matrixInner E M = nuclearNorm M := by
    rw [hE]; exact sign_matrix_inner_eq_nuclear_norm S
  have hEH : matrixInner E H = matrixInner E (tangentProjection S H) := by
    have hEt : tangentProjection S E = E := by
      rw [hE]; unfold tangentProjection; rw [left_signMatrix, right_signMatrix, two_signMatrix]; abel
    calc matrixInner E H = matrixInner (tangentProjection S E) H := by rw [hEt]
      _ = matrixInner E (tangentProjection S H) := (tangentProjection_selfAdjoint S E H).symm
  have hPTW : tangentProjection S W = 0 := by
    have hdef : normalProjection S W = W - tangentProjection S W := rfl
    rw [hdef] at hWT
    exact sub_eq_self.mp hWT
  have hWM : matrixInner W M = 0 := by
    have hPTM : tangentProjection S M = M := tangent_M S
    calc matrixInner W M = matrixInner W (tangentProjection S M) := by rw [hPTM]
      _ = matrixInner (tangentProjection S W) M := (tangentProjection_selfAdjoint S W M)
      _ = matrixInner (0 : RealMatrix n₁ n₂) M := by rw [hPTW]
      _ = 0 := by unfold matrixInner; simp
  have hWH : matrixInner W H = nuclearNorm (normalProjection S H) := by
    have hsplit : H = tangentProjection S H + normalProjection S H := by
      have : normalProjection S H = H - tangentProjection S H := rfl
      rw [this]; abel
    have hWPTH : matrixInner W (tangentProjection S H) = 0 := by
      calc matrixInner W (tangentProjection S H)
          = matrixInner (tangentProjection S W) H := (tangentProjection_selfAdjoint S W H)
        _ = matrixInner (0 : RealMatrix n₁ n₂) H := by rw [hPTW]
        _ = 0 := by unfold matrixInner; simp
    calc matrixInner W H
        = matrixInner W (tangentProjection S H + normalProjection S H) := by rw [← hsplit]
      _ = matrixInner W (tangentProjection S H) + matrixInner W (normalProjection S H) :=
            matrixInner_add_right W _ _
      _ = 0 + matrixInner W (normalProjection S H) := by rw [hWPTH]
      _ = matrixInner W (normalProjection S H) := by rw [zero_add]
      _ = nuclearNorm (normalProjection S H) := hWNH
  rw [hexp, hEM, hEH, hWM, hWH] at hub
  linarith [hub]
