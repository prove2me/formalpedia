-- Prove2me | solution 2 for tangent_sampling_deviation_candidates_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T14:58:26.761478+00:00
-- url     : https://prove2.me/submissions/f7131204-cd7a-4da5-b5d7-881d15ae34d9

import Definitions.Def_matrix_completion_tangent
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.MeanInequalities

open MatrixCompletion
open scoped Classical BigOperators

namespace MatrixCompletion

/-! ## Frobenius-norm helpers (self-contained) -/

theorem bdd_frobeniusNormSq_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ frobeniusNormSq X :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem bdd_frobeniusNorm_as_rpow {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    frobeniusNorm X
      = (∑ q : Fin n1 × Fin n2, |X q.1 q.2| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  unfold frobeniusNorm frobeniusNormSq
  rw [Real.sqrt_eq_rpow]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  show X i j ^ 2 = |X i j| ^ (2 : ℝ)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

theorem bdd_frobeniusNorm_triangle {n1 n2 : Nat} (A B : RealMatrix n1 n2) :
    frobeniusNorm (A + B) ≤ frobeniusNorm A + frobeniusNorm B := by
  rw [bdd_frobeniusNorm_as_rpow, bdd_frobeniusNorm_as_rpow, bdd_frobeniusNorm_as_rpow]
  have hadd : ∀ q : Fin n1 × Fin n2, (A + B) q.1 q.2 = A q.1 q.2 + B q.1 q.2 := by
    intro q; simp [Matrix.add_apply]
  have hmink := Real.Lp_add_le (p := (2:ℝ)) (Finset.univ : Finset (Fin n1 × Fin n2))
      (fun q => A q.1 q.2) (fun q => B q.1 q.2) (by norm_num)
  simp_rw [hadd]
  exact hmink

theorem bdd_frobeniusNormSq_smul {n1 n2 : Nat} (c : ℝ) (X : RealMatrix n1 n2) :
    frobeniusNormSq (c • X) = c ^ 2 * frobeniusNormSq X := by
  unfold frobeniusNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.smul_apply, smul_eq_mul]; ring

theorem bdd_frobeniusNorm_smul {n1 n2 : Nat} (c : ℝ) (X : RealMatrix n1 n2) :
    frobeniusNorm (c • X) = |c| * frobeniusNorm X := by
  unfold frobeniusNorm
  rw [bdd_frobeniusNormSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem bdd_frobeniusNorm_neg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    frobeniusNorm (-X) = frobeniusNorm X := by
  have : (-X) = ((-1 : ℝ)) • X := by
    funext i j; simp [Matrix.neg_apply, Matrix.smul_apply]
  rw [this, bdd_frobeniusNorm_smul]; simp

theorem bdd_frobeniusNorm_sub_le {n1 n2 : Nat} (A B : RealMatrix n1 n2) :
    frobeniusNorm (A - B) ≤ frobeniusNorm A + frobeniusNorm B := by
  rw [sub_eq_add_neg]
  calc frobeniusNorm (A + (-B)) ≤ frobeniusNorm A + frobeniusNorm (-B) :=
        bdd_frobeniusNorm_triangle A (-B)
    _ = frobeniusNorm A + frobeniusNorm B := by rw [bdd_frobeniusNorm_neg]

theorem bdd_samplingProjection_contraction_sq {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    frobeniusNormSq (samplingProjection Omega X) ≤ frobeniusNormSq X := by
  unfold frobeniusNormSq samplingProjection
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  by_cases h : (i, j) ∈ Omega <;> simp [h, sq_nonneg]

theorem bdd_samplingProjection_contraction {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    frobeniusNorm (samplingProjection Omega X) ≤ frobeniusNorm X := by
  unfold frobeniusNorm
  exact Real.sqrt_le_sqrt (bdd_samplingProjection_contraction_sq Omega X)

/-! ## Tangent projection contraction (squared, then sqrt) — operator-algebra route -/

theorem bdd_ker_idem {N r : Nat} (u : Fin r → (Fin N → ℝ))
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

theorem bdd_left_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
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
    rw [bdd_ker_idem S.u S.u_orthonormal i a]
  exact this

theorem bdd_right_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
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
  rw [bdd_ker_idem S.v S.v_orthonormal c j]

theorem bdd_two_eq_left_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = leftSingularProjection S (rightSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem bdd_two_eq_right_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = rightSingularProjection S (leftSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

theorem bdd_left_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B) = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  unfold leftSingularProjection
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem bdd_left_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B) = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  unfold leftSingularProjection
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem bdd_right_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B) = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  unfold rightSingularProjection
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem bdd_right_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B) = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  unfold rightSingularProjection
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem bdd_left_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [bdd_two_eq_left_right S X, bdd_left_left S (rightSingularProjection S X)]

theorem bdd_right_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [bdd_two_eq_right_left S X, bdd_right_right S (leftSingularProjection S X)]

theorem bdd_left_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (tangentProjection S X) = leftSingularProjection S X := by
  unfold tangentProjection
  rw [bdd_left_sub, bdd_left_add, bdd_left_left, ← bdd_two_eq_left_right, bdd_left_two]
  abel

theorem bdd_right_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (tangentProjection S X) = rightSingularProjection S X := by
  unfold tangentProjection
  rw [bdd_right_sub, bdd_right_add, bdd_right_right, ← bdd_two_eq_right_left, bdd_right_two]
  abel

theorem bdd_two_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (tangentProjection S X) = twoSidedSingularProjection S X := by
  rw [bdd_two_eq_left_right S (tangentProjection S X), bdd_right_tangent, ← bdd_two_eq_left_right]

theorem bdd_tangent_idem {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  conv_lhs => rw [tangentProjection]
  rw [bdd_left_tangent, bdd_right_tangent, bdd_two_tangent]
  rfl

theorem bdd_matrixInner_self {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    matrixInner X X = frobeniusNormSq X := by
  unfold matrixInner frobeniusNormSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

theorem bdd_matrixInner_sq_le {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
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

theorem bdd_tangentProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
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

theorem bdd_tangentProjection_contraction_sq {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) :
    frobeniusNormSq (tangentProjection S X) ≤ frobeniusNormSq X := by
  set Y := tangentProjection S X with hY
  have hself : matrixInner Y Y = matrixInner X Y := by
    have hsa := bdd_tangentProjection_selfAdjoint S X Y
    rw [hY] at hsa
    rw [bdd_tangent_idem] at hsa
    rw [hY]; exact hsa.symm
  have hYY : frobeniusNormSq Y = matrixInner X Y := by
    rw [← bdd_matrixInner_self Y, hself]
  have hcs : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y :=
    bdd_matrixInner_sq_le X Y
  have hYYnn : 0 ≤ frobeniusNormSq Y := bdd_frobeniusNormSq_nonneg Y
  have hXXnn : 0 ≤ frobeniusNormSq X := bdd_frobeniusNormSq_nonneg X
  have hsq : (frobeniusNormSq Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    calc (frobeniusNormSq Y) ^ 2 = (matrixInner X Y) ^ 2 := by rw [hYY]
      _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hcs
  rcases eq_or_lt_of_le hYYnn with h0 | hpos
  · rw [← h0]; exact hXXnn
  · have : frobeniusNormSq Y * frobeniusNormSq Y ≤ frobeniusNormSq X * frobeniusNormSq Y := by
      calc frobeniusNormSq Y * frobeniusNormSq Y = (frobeniusNormSq Y) ^ 2 := by ring
        _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hsq
    exact le_of_mul_le_mul_right this hpos

theorem bdd_tangentProjection_contraction {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) :
    frobeniusNorm (tangentProjection S X) ≤ frobeniusNorm X := by
  unfold frobeniusNorm
  exact Real.sqrt_le_sqrt (bdd_tangentProjection_contraction_sq S X)

end MatrixCompletion

/-! ## The bddAbove theorem -/

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    BddAbove {v : ℝ |
      ∃ X : Matrix (Fin n₁) (Fin n₂) ℝ,
        tangentProjection S X = X ∧ frobeniusNorm X ≤ 1 ∧
          v = (p⁻¹) *
            frobeniusNorm
              (tangentProjection S (samplingProjection Omega X) - p • X)} := by
  refine ⟨|p⁻¹| * (1 + |p|), ?_⟩
  rintro v ⟨X, hPX, hX1, hv⟩
  rw [hv]
  -- bound the frobenius norm part by 1 + |p|
  have hbound : frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
      ≤ 1 + |p| := by
    calc frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
        ≤ frobeniusNorm (tangentProjection S (samplingProjection Omega X))
            + frobeniusNorm (p • X) :=
          bdd_frobeniusNorm_sub_le _ _
      _ ≤ frobeniusNorm (samplingProjection Omega X) + |p| * frobeniusNorm X := by
          gcongr
          · exact bdd_tangentProjection_contraction S (samplingProjection Omega X)
          · rw [bdd_frobeniusNorm_smul]
      _ ≤ frobeniusNorm X + |p| * frobeniusNorm X := by
          gcongr
          exact bdd_samplingProjection_contraction Omega X
      _ ≤ 1 + |p| * 1 := by
          gcongr
      _ = 1 + |p| := by ring
  -- now p⁻¹ * (norm) ≤ |p⁻¹| * (1+|p|)
  calc p⁻¹ * frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
      ≤ |p⁻¹| * frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X) := by
        gcongr
        · exact Real.sqrt_nonneg _
        · exact le_abs_self _
    _ ≤ |p⁻¹| * (1 + |p|) := by
        gcongr
