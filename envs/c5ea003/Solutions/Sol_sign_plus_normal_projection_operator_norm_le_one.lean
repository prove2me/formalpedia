-- Prove2me | solution 1 for sign_plus_normal_projection_operator_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T22:25:24.331119+00:00
-- url     : https://prove2.me/submissions/eada214d-0429-450f-9666-6dd107c01ffc

import Theorems.Thm_sign_matrix_spectral_norm_le_one
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

namespace MatrixCompletion
open scoped Classical BigOperators
open Matrix LinearMap Module InnerProductSpace WithLp

variable {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂}

theorem signMatrix_spectralNorm_le_one_stub (S : SVD M r) :
    spectralNorm (signMatrix S) ≤ 1 :=
  sign_matrix_spectral_norm_le_one S

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


theorem left_signMatrix (S : SVD M r) :
    leftSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold leftSingularProjection signMatrix
  -- signMatrix a j = ∑ l, u l a * v l j
  have hsm : ∀ a : Fin n₁, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) a j
      = ∑ l : Fin r, S.u l a * S.v l j := by
    intro a
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  -- LHS = ∑ a (∑ k u_k i u_k a)(∑ l u_l a v_l j)
  -- = ∑ k u_k i v_k j  (orthonormality of u)
  have hgoal : (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
        = ∑ a : Fin n₁, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j) := by
      apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ k : Fin r, ∑ a : Fin n₁, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n₁, S.u k a * S.u l a) := by
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
    rw [e2]
    have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n₁, S.u k a * S.u l a))
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
  have hsm : ∀ b : Fin n₂, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) i b
      = ∑ l : Fin r, S.u l i * S.v l b := by
    intro b
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _; rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  have hgoal : (∑ b : Fin n₂, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ b : Fin n₂, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
        = ∑ b : Fin n₂, ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j) := by
      apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ l : Fin r, ∑ b : Fin n₂, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n₂, S.v l b * S.v k b) := by
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e2]
    have e3 : (∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n₂, S.v l b * S.v k b))
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

/-! ## Matrix projectors PU (n₁×n₁) and PV (n₂×n₂). -/

/-- Orthogonal projector onto the column singular space. -/
noncomputable def PUmat (S : SVD M r) : Matrix (Fin n₁) (Fin n₁) ℝ :=
  ∑ k, Matrix.vecMulVec (S.u k) (S.u k)

/-- Orthogonal projector onto the row singular space. -/
noncomputable def PVmat (S : SVD M r) : Matrix (Fin n₂) (Fin n₂) ℝ :=
  ∑ k, Matrix.vecMulVec (S.v k) (S.v k)

theorem PUmat_apply (S : SVD M r) (i a : Fin n₁) :
    PUmat S i a = ∑ k, S.u k i * S.u k a := by
  unfold PUmat
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _; rw [Matrix.vecMulVec_apply]

theorem PVmat_apply (S : SVD M r) (b j : Fin n₂) :
    PVmat S b j = ∑ k, S.v k b * S.v k j := by
  unfold PVmat
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _; rw [Matrix.vecMulVec_apply]

/-! ## Projector forms of the singular projections. -/

theorem left_eq_PU (S : SVD M r) (X : RealMatrix n₁ n₂) :
    leftSingularProjection S X = PUmat S * X := by
  funext i j
  unfold leftSingularProjection
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply]

theorem right_eq_PV (S : SVD M r) (X : RealMatrix n₁ n₂) :
    rightSingularProjection S X = X * PVmat S := by
  funext i j
  unfold rightSingularProjection
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro b _; rw [PVmat_apply]

theorem two_eq_PU_PV (S : SVD M r) (X : RealMatrix n₁ n₂) :
    twoSidedSingularProjection S X = PUmat S * X * PVmat S := by
  funext i j
  unfold twoSidedSingularProjection
  rw [Matrix.mul_apply]
  -- (PU * X * PV) i j = ∑ b (PU*X) i b * PV b j = ∑ b (∑ a PU i a * X a b) * PV b j
  have hrew : ∀ b : Fin n₂, (PUmat S * X) i b * PVmat S b j
      = (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * X a b)
          * (∑ l : Fin r, S.v l b * S.v l j) := by
    intro b
    rw [Matrix.mul_apply, PVmat_apply]
    congr 1
    apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply]
  rw [Finset.sum_congr rfl (fun b _ => hrew b)]
  -- target: ∑ a ∑ b (∑k u i a) X a b (∑l v b j) = ∑ b (∑ a (∑k u i a) X a b)(∑l v b j)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

/-! ## Idempotence and symmetry of PU, PV. -/

theorem PU_idem (S : SVD M r) : PUmat S * PUmat S = PUmat S := by
  funext i j
  rw [Matrix.mul_apply]
  have : (∑ a : Fin n₁, PUmat S i a * PUmat S a j)
      = ∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.u l j) := by
    apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply, PUmat_apply]
  rw [this, ker_idem S.u S.u_orthonormal i j, PUmat_apply]

theorem PV_idem (S : SVD M r) : PVmat S * PVmat S = PVmat S := by
  funext i j
  rw [Matrix.mul_apply]
  have : (∑ a : Fin n₂, PVmat S i a * PVmat S a j)
      = ∑ a : Fin n₂, (∑ k : Fin r, S.v k i * S.v k a) * (∑ l : Fin r, S.v l a * S.v l j) := by
    apply Finset.sum_congr rfl; intro a _; rw [PVmat_apply, PVmat_apply]
  rw [this, ker_idem S.v S.v_orthonormal i j, PVmat_apply]

theorem PU_symm (S : SVD M r) : (PUmat S)ᵀ = PUmat S := by
  funext i j
  rw [Matrix.transpose_apply, PUmat_apply, PUmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

theorem PV_symm (S : SVD M r) : (PVmat S)ᵀ = PVmat S := by
  funext i j
  rw [Matrix.transpose_apply, PVmat_apply, PVmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

/-! ## Factorization of the normal projection: W = (1-PU) Z (1-PV). -/

theorem normalProjection_factor (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    normalProjection S Z = (1 - PUmat S) * Z * (1 - PVmat S) := by
  unfold normalProjection tangentProjection
  rw [left_eq_PU, right_eq_PV, two_eq_PU_PV]
  -- Z - (PU Z + Z PV - PU Z PV) = (1-PU) Z (1-PV)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  -- LHS = Z - (PU*Z + Z*PV - PU*Z*PV); RHS = (Z - Z*PV) - (PU*Z - PU*Z*PV)
  abel

/-! ## E = signMatrix S obeys PU E = E, E PV = E. -/

theorem PU_signMatrix (S : SVD M r) : PUmat S * signMatrix S = signMatrix S := by
  rw [← left_eq_PU, left_signMatrix]

theorem signMatrix_PV (S : SVD M r) : signMatrix S * PVmat S = signMatrix S := by
  rw [← right_eq_PV, right_signMatrix]

/-! ## Orthogonality crux: Eᵀ * W = 0  and  W * PV = 0. -/

theorem Etrans_W_eq_zero (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    (signMatrix S)ᵀ * normalProjection S Z = 0 := by
  rw [normalProjection_factor]
  -- Eᵀ * (1-PU) * Z * (1-PV) ; Eᵀ * (1-PU) = Eᵀ - Eᵀ PU = Eᵀ - (PU E)ᵀ = Eᵀ - Eᵀ = 0
  have hEt : (signMatrix S)ᵀ * (1 - PUmat S) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have : (signMatrix S)ᵀ * PUmat S = (signMatrix S)ᵀ := by
      have h := PU_signMatrix S
      have h2 : (PUmat S * signMatrix S)ᵀ = (signMatrix S)ᵀ := by rw [h]
      rw [Matrix.transpose_mul, PU_symm] at h2
      exact h2
    rw [this, sub_self]
  calc (signMatrix S)ᵀ * ((1 - PUmat S) * Z * (1 - PVmat S))
      = ((signMatrix S)ᵀ * (1 - PUmat S)) * Z * (1 - PVmat S) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = 0 := by rw [hEt, Matrix.zero_mul, Matrix.zero_mul]

theorem W_PV_eq_zero (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    normalProjection S Z * PVmat S = 0 := by
  rw [normalProjection_factor]
  have hPV : (1 - PVmat S) * PVmat S = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, PV_idem, sub_self]
  calc (1 - PUmat S) * Z * (1 - PVmat S) * PVmat S
      = (1 - PUmat S) * Z * ((1 - PVmat S) * PVmat S) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hPV, Matrix.mul_zero]

/-! ## E = E PV (already from right_signMatrix). -/

theorem signMatrix_eq_signMatrix_PV (S : SVD M r) :
    signMatrix S = signMatrix S * PVmat S := (signMatrix_PV S).symm

/-! ## Analytic part. -/

/-- ofLp of the Euclidean image is the matrix-vector product. -/
theorem ofLp_image (A : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    ofLp ((toEuclideanLin A) x) = A *ᵥ ofLp x :=
  Matrix.ofLp_toEuclideanLin_apply A x

/-- Euclidean inner product as coordinate sum (for ℝ). -/
theorem eucl_inner_eq_sum {N : ℕ} (a b : EuclideanSpace ℝ (Fin N)) :
    (inner ℝ a b : ℝ) = ∑ i, (ofLp a) i * (ofLp b) i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl; intro i _
  rw [show (⟪a i, b i⟫_ℝ : ℝ) = b i * (starRingEnd ℝ) (a i) from RCLike.inner_apply _ _,
      conj_trivial]; ring

/-- Inner product of two Euclidean images as a coordinate sum of matrix-vector products. -/
theorem inner_image_eq_sum (B C : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    (inner ℝ ((toEuclideanLin B) x) ((toEuclideanLin C) x) : ℝ)
      = ∑ i, (B *ᵥ ofLp x) i * (C *ᵥ ofLp x) i := by
  rw [eucl_inner_eq_sum, ofLp_image, ofLp_image]

/-- A bilinear quadratic form `∑ᵢ (B x)ᵢ (C x)ᵢ` expands as `∑_{p,q} (Bᵀ C)_{pq} xₚ x_q`. -/
theorem mulVec_dot_eq_transpose_mul (B C : RealMatrix n₁ n₂) (x : Fin n₂ → ℝ) :
    (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ p, ∑ q, (Bᵀ * C) p q * x p * x q := by
  have e1 : (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ i, (∑ p, B i p * x p) * (∑ q, C i q * x q) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.mulVec, Matrix.mulVec]; rfl
  rw [e1]
  -- expand each product, swap sums to pull i innermost
  have e2 : (∑ i, (∑ p, B i p * x p) * (∑ q, C i q * x q))
      = ∑ i, ∑ p, ∑ q, (B i p * C i q) * (x p * x q) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _; ring
  rw [e2, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q _
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.transpose_apply]; ring

/-- If `Bᵀ C = 0` then `∑ᵢ (B x)ᵢ (C x)ᵢ = 0`. -/
theorem mulVec_dot_eq_zero_of_transpose_mul_zero (B C : RealMatrix n₁ n₂)
    (h : Bᵀ * C = 0) (x : Fin n₂ → ℝ) :
    (∑ i, (B *ᵥ x) i * (C *ᵥ x) i) = 0 := by
  rw [mulVec_dot_eq_transpose_mul, h]
  simp

/-! ## Euclidean norm-squared as a quadratic form. -/

/-- `‖a‖² = ∑ᵢ (ofLp a)ᵢ²`. -/
theorem normSq_eq_sum {N : ℕ} (a : EuclideanSpace ℝ (Fin N)) :
    ‖a‖ ^ 2 = ∑ i, (ofLp a) i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, eucl_inner_eq_sum]
  apply Finset.sum_congr rfl; intro i _; ring

/-- `‖B y‖² = ∑_{p,q} (Bᵀ B)_{pq} yₚ y_q` for the Euclidean image. -/
theorem normSq_image_eq_quad (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ^ 2
      = ∑ p, ∑ q, (Bᵀ * B) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  have : (∑ i, (ofLp ((toEuclideanLin B) y)) i ^ 2)
      = ∑ i, (B *ᵥ ofLp y) i * (B *ᵥ ofLp y) i := by
    apply Finset.sum_congr rfl; intro i _; rw [ofLp_image]; ring
  rw [this, mulVec_dot_eq_transpose_mul]

/-- `‖y‖² = ∑_{p,q} (1)_{pq} yₚ y_q`. -/
theorem normSq_eq_one_quad {N : ℕ} (y : EuclideanSpace ℝ (Fin N)) :
    ‖y‖ ^ 2 = ∑ p, ∑ q, (1 : Matrix (Fin N) (Fin N) ℝ) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq]; ring
  · intro q _ hq; rw [Matrix.one_apply_ne (Ne.symm hq)]; ring
  · intro h; exact absurd (Finset.mem_univ p) h

/-- Pythagorean split for a symmetric idempotent square matrix `P`. -/
theorem pythagoras_split {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin P) y‖ ^ 2 + ‖(toEuclideanLin (1 - P)) y‖ ^ 2 = ‖y‖ ^ 2 := by
  have hPtP : Pᵀ * P = P := by rw [hsymm, hidem]
  have hQtQ : (1 - P)ᵀ * (1 - P) = 1 - P := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hidem]
    abel
  rw [normSq_image_eq_quad, hPtP, normSq_image_eq_quad, hQtQ, normSq_eq_one_quad]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases h : p = q
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-! ## Operator-norm bound transport. -/

/-- `‖B y‖ ≤ spectralNorm B · ‖y‖`. -/
theorem norm_image_le (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ≤ spectralNorm B * ‖y‖ := by
  unfold spectralNorm
  have h := (LinearMap.toContinuousLinearMap (toEuclideanLin B)).le_opNorm y
  simpa using h

/-- Orthogonal projection `1-P` (symmetric idempotent `P`) is a contraction. -/
theorem norm_compl_le {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin (1 - P)) y‖ ≤ ‖y‖ := by
  have hsplit := pythagoras_split P hsymm hidem y
  have hle : ‖(toEuclideanLin (1 - P)) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(toEuclideanLin P) y‖]
  have h1 := norm_nonneg ((toEuclideanLin (1 - P)) y)
  have h2 := norm_nonneg y
  nlinarith [hle, h1, h2]

/-! ## `toEuclideanLin` is multiplicative / additive (transported through `ofLp`). -/

theorem toEuclideanLin_mul_apply {n₀ : ℕ} (A : RealMatrix n₀ n₁) (B : RealMatrix n₁ n₂)
    (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (A * B)) x = (toEuclideanLin A) ((toEuclideanLin B) x) := by
  apply ofLp_injective
  rw [ofLp_image, ofLp_image, ofLp_image, Matrix.mulVec_mulVec]

theorem toEuclideanLin_add_apply (A B : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (A + B)) x = (toEuclideanLin A) x + (toEuclideanLin B) x := by
  apply ofLp_injective
  rw [ofLp_image]
  rw [show ofLp ((toEuclideanLin A) x + (toEuclideanLin B) x)
        = ofLp ((toEuclideanLin A) x) + ofLp ((toEuclideanLin B) x) from rfl]
  rw [ofLp_image, ofLp_image, Matrix.add_mulVec]

/-! ## The per-vector contraction, then the operator-norm bound. -/

/-- Per-vector sharp contraction: `‖(E + W) x‖ ≤ ‖x‖` in EuclideanSpace. -/
theorem nopb_vector (S : SVD M r) (Z : RealMatrix n₁ n₂) (hZ : spectralNorm Z ≤ 1)
    (x : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin (signMatrix S + normalProjection S Z)) x‖ ≤ ‖x‖ := by
  set E := signMatrix S with hE
  set W := normalProjection S Z with hW
  set Ex := (toEuclideanLin E) x with hEx
  set Wx := (toEuclideanLin W) x with hWx
  -- A x = E x + W x
  have hAx : (toEuclideanLin (E + W)) x = Ex + Wx := toEuclideanLin_add_apply E W x
  -- orthogonality ⟪Ex, Wx⟫ = 0
  have horth : (inner ℝ Ex Wx : ℝ) = 0 := by
    rw [hEx, hWx, inner_image_eq_sum]
    exact mulVec_dot_eq_zero_of_transpose_mul_zero E W (Etrans_W_eq_zero S Z) (ofLp x)
  -- Pythagoras
  have hpyth : ‖Ex + Wx‖ ^ 2 = ‖Ex‖ ^ 2 + ‖Wx‖ ^ 2 := by
    rw [norm_add_sq_real, horth]; ring
  -- ‖Ex‖ ≤ ‖PV x‖
  have hEbound : ‖Ex‖ ≤ ‖(toEuclideanLin (PVmat S)) x‖ := by
    have hsplit : E = E * PVmat S := signMatrix_eq_signMatrix_PV S
    have : Ex = (toEuclideanLin E) ((toEuclideanLin (PVmat S)) x) := by
      rw [hEx]
      conv_lhs => rw [hsplit]
      rw [toEuclideanLin_mul_apply]
    rw [this]
    calc ‖(toEuclideanLin E) ((toEuclideanLin (PVmat S)) x)‖
        ≤ spectralNorm E * ‖(toEuclideanLin (PVmat S)) x‖ := norm_image_le E _
      _ ≤ 1 * ‖(toEuclideanLin (PVmat S)) x‖ := by
          apply mul_le_mul_of_nonneg_right (signMatrix_spectralNorm_le_one_stub S) (norm_nonneg _)
      _ = ‖(toEuclideanLin (PVmat S)) x‖ := one_mul _
  -- ‖Wx‖ ≤ ‖(1-PV) x‖
  have hWbound : ‖Wx‖ ≤ ‖(toEuclideanLin (1 - PVmat S)) x‖ := by
    -- W = (1-PU) Z (1-PV), so W x = (1-PU)(Z((1-PV)x))
    have hWfac : W = (1 - PUmat S) * Z * (1 - PVmat S) := normalProjection_factor S Z
    have hWx2 : Wx = (toEuclideanLin (1 - PUmat S))
        ((toEuclideanLin Z) ((toEuclideanLin (1 - PVmat S)) x)) := by
      rw [hWx, hWfac, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    rw [hWx2]
    have hPUsymm : (PUmat S)ᵀ = PUmat S := PU_symm S
    have hPUidem : PUmat S * PUmat S = PUmat S := PU_idem S
    calc ‖(toEuclideanLin (1 - PUmat S))
            ((toEuclideanLin Z) ((toEuclideanLin (1 - PVmat S)) x))‖
        ≤ ‖(toEuclideanLin Z) ((toEuclideanLin (1 - PVmat S)) x)‖ :=
          norm_compl_le (PUmat S) hPUsymm hPUidem _
      _ ≤ spectralNorm Z * ‖(toEuclideanLin (1 - PVmat S)) x‖ := norm_image_le Z _
      _ ≤ 1 * ‖(toEuclideanLin (1 - PVmat S)) x‖ := by
          apply mul_le_mul_of_nonneg_right hZ (norm_nonneg _)
      _ = ‖(toEuclideanLin (1 - PVmat S)) x‖ := one_mul _
  -- Pythagoras split for PV
  have hPVsplit : ‖(toEuclideanLin (PVmat S)) x‖ ^ 2
      + ‖(toEuclideanLin (1 - PVmat S)) x‖ ^ 2 = ‖x‖ ^ 2 :=
    pythagoras_split (PVmat S) (PV_symm S) (PV_idem S) x
  -- combine
  have hAsq : ‖(toEuclideanLin (E + W)) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hAx, hpyth]
    have h1 : ‖Ex‖ ^ 2 ≤ ‖(toEuclideanLin (PVmat S)) x‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg Ex) hEbound 2
    have h2 : ‖Wx‖ ^ 2 ≤ ‖(toEuclideanLin (1 - PVmat S)) x‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg Wx) hWbound 2
    nlinarith [h1, h2, hPVsplit]
  -- conclude ‖A x‖ ≤ ‖x‖
  have hAnn := norm_nonneg ((toEuclideanLin (E + W)) x)
  have hxnn := norm_nonneg x
  nlinarith [hAsq, hAnn, hxnn]

/-- **nopb** — sign + normal projection contraction:
`spectralNorm (signMatrix S + normalProjection S Z) ≤ 1` when `spectralNorm Z ≤ 1`.
Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2 achiever contraction. -/
theorem nopb {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (Z : Matrix (Fin n₁) (Fin n₂) ℝ) (hZ : spectralNorm Z ≤ 1) :
    spectralNorm (signMatrix S + normalProjection S Z) ≤ 1 := by
  unfold spectralNorm
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul]
  have h := nopb_vector S Z hZ x
  simpa using h


end MatrixCompletion

open MatrixCompletion
theorem solution {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (Z : Matrix (Fin n₁) (Fin n₂) ℝ) (hZ : spectralNorm Z ≤ 1) :
    spectralNorm (signMatrix S + normalProjection S Z) ≤ 1 :=
  MatrixCompletion.nopb S Z hZ
