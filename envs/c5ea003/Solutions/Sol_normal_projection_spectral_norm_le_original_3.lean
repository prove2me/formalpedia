-- Prove2me | solution 3 for normal_projection_spectral_norm_le_original
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-22T02:41:59.323933+00:00
-- url     : https://prove2.me/submissions/6416db6b-ff46-4a7c-abb7-960cdbb80014

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

namespace MatrixCompletion
open scoped Classical BigOperators
open Matrix LinearMap Module InnerProductSpace WithLp
variable {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂}

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

theorem toEuclideanLin_mul_apply {n₀ : ℕ} (A : RealMatrix n₀ n₁) (B : RealMatrix n₁ n₂)
    (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (A * B)) x = (toEuclideanLin A) ((toEuclideanLin B) x) := by
  apply ofLp_injective
  rw [ofLp_image, ofLp_image, ofLp_image, Matrix.mulVec_mulVec]

/-- `‖PV x‖ ≤ ‖x‖`: the projector `PVmat` is a spectral-norm contraction. -/
theorem norm_PV_le (S : SVD M r) (x : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin (PVmat S)) x‖ ≤ ‖x‖ := by
  have hsplit := pythagoras_split (PVmat S) (PV_symm S) (PV_idem S) x
  have hle : ‖(toEuclideanLin (PVmat S)) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(toEuclideanLin (1 - PVmat S)) x‖]
  have h1 := norm_nonneg ((toEuclideanLin (PVmat S)) x)
  have h2 := norm_nonneg x
  nlinarith [hle, h1, h2]

/-- Per-vector bound for `(1-PU) X Q` with `Q` a contraction sending `x ↦ Qx`,
    given `‖Q x‖ ≤ ‖x‖`. -/
theorem complLeft_times_apply_le
    (S : SVD M r) (X : RealMatrix n₁ n₂) (Q : Matrix (Fin n₂) (Fin n₂) ℝ)
    (x : EuclideanSpace ℝ (Fin n₂)) (hQ : ‖(toEuclideanLin Q) x‖ ≤ ‖x‖) :
    ‖(toEuclideanLin ((1 - PUmat S) * X * Q)) x‖ ≤ spectralNorm X * ‖x‖ := by
  have happ : (toEuclideanLin ((1 - PUmat S) * X * Q)) x
      = (toEuclideanLin (1 - PUmat S)) ((toEuclideanLin X) ((toEuclideanLin Q) x)) := by
    rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
  rw [happ]
  calc ‖(toEuclideanLin (1 - PUmat S)) ((toEuclideanLin X) ((toEuclideanLin Q) x))‖
      ≤ ‖(toEuclideanLin X) ((toEuclideanLin Q) x)‖ :=
        norm_compl_le (PUmat S) (PU_symm S) (PU_idem S) _
    _ ≤ spectralNorm X * ‖(toEuclideanLin Q) x‖ := norm_image_le X _
    _ ≤ spectralNorm X * ‖x‖ := by
        apply mul_le_mul_of_nonneg_left hQ
        unfold spectralNorm; exact norm_nonneg _

/-- Operator-norm bound for `(1-PU) X Q` when `Q` contracts: `‖(1-PU)XQ‖ ≤ ‖X‖`. -/
theorem complLeft_times_spectralNorm_le
    (S : SVD M r) (X : RealMatrix n₁ n₂) (Q : Matrix (Fin n₂) (Fin n₂) ℝ)
    (hQ : ∀ x : EuclideanSpace ℝ (Fin n₂), ‖(toEuclideanLin Q) x‖ ≤ ‖x‖) :
    spectralNorm ((1 - PUmat S) * X * Q) ≤ spectralNorm X := by
  unfold spectralNorm
  apply ContinuousLinearMap.opNorm_le_bound
  · exact norm_nonneg _
  · intro x
    have h := complLeft_times_apply_le S X Q x (hQ x)
    -- h : ‖...‖ ≤ spectralNorm X * ‖x‖, and spectralNorm X unfolds to the opNorm of X
    simpa [spectralNorm] using h

/-! ## 7898c9b3 / 2a6bfd25 — `(1-PU) X (1-PV)`. -/

/-- The inclusion-exclusion form equals `(1-PU) X (1-PV)`. -/
theorem incl_excl_eq_factor (S : SVD M r) (X : RealMatrix n₁ n₂) :
    X - leftSingularProjection S X - rightSingularProjection S X
        + twoSidedSingularProjection S X
      = (1 - PUmat S) * X * (1 - PVmat S) := by
  rw [left_eq_PU, right_eq_PV, two_eq_PU_PV]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  abel

/-- **7898c9b3** singular_projection_inclusion_exclusion_spectral_norm_le_original. -/
theorem incl_excl_spectralNorm_le (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm
        (X - leftSingularProjection S X - rightSingularProjection S X
          + twoSidedSingularProjection S X) ≤ spectralNorm X := by
  rw [incl_excl_eq_factor]
  exact complLeft_times_spectralNorm_le S X (1 - PVmat S)
    (fun x => norm_compl_le (PVmat S) (PV_symm S) (PV_idem S) x)

/-- **2a6bfd25** normal_projection_spectral_norm_le_original. -/
theorem normalProjection_spectralNorm_le (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm (normalProjection S X) ≤ spectralNorm X := by
  rw [normalProjection_factor]
  exact complLeft_times_spectralNorm_le S X (1 - PVmat S)
    (fun x => norm_compl_le (PVmat S) (PV_symm S) (PV_idem S) x)

/-! ## 948a9c8d — `rightSingularProjection - twoSidedSingularProjection = (1-PU) X PV`. -/

theorem right_minus_two_eq_factor (S : SVD M r) (X : RealMatrix n₁ n₂) :
    rightSingularProjection S X - twoSidedSingularProjection S X
      = (1 - PUmat S) * X * PVmat S := by
  rw [right_eq_PV, two_eq_PU_PV, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul]

/-- **948a9c8d** right_singular_projection_minus_two_sided_spectral_norm_le_original. -/
theorem right_minus_two_spectralNorm_le (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm (rightSingularProjection S X - twoSidedSingularProjection S X)
      ≤ spectralNorm X := by
  rw [right_minus_two_eq_factor]
  exact complLeft_times_spectralNorm_le S X (PVmat S) (fun x => norm_PV_le S x)

/-! ## dc89d139 — `‖P_T X‖ ≤ 2 ‖X‖`. -/

/-- `tangentProjection S X = PU X + (1-PU) X PV`. -/
theorem tangentProjection_split (S : SVD M r) (X : RealMatrix n₁ n₂) :
    tangentProjection S X = PUmat S * X + (1 - PUmat S) * X * PVmat S := by
  unfold tangentProjection
  rw [left_eq_PU, right_eq_PV, two_eq_PU_PV]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul]
  abel

/-- `‖PU y‖ ≤ ‖y‖` (projector `PUmat` is a spectral-norm contraction). -/
theorem norm_PU_le (S : SVD M r) (y : EuclideanSpace ℝ (Fin n₁)) :
    ‖(toEuclideanLin (PUmat S)) y‖ ≤ ‖y‖ := by
  have hsplit := pythagoras_split (PUmat S) (PU_symm S) (PU_idem S) y
  have hle : ‖(toEuclideanLin (PUmat S)) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(toEuclideanLin (1 - PUmat S)) y‖]
  have a1 := norm_nonneg ((toEuclideanLin (PUmat S)) y)
  have a2 := norm_nonneg y
  nlinarith [hle, a1, a2]

/-- `‖PU X‖ ≤ ‖X‖` (left multiplication by a projector contracts spectrally). -/
theorem norm_PU_mul_le (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm (PUmat S * X) ≤ spectralNorm X := by
  unfold spectralNorm
  apply ContinuousLinearMap.opNorm_le_bound
  · exact norm_nonneg _
  · intro x
    have happ : (toEuclideanLin (PUmat S * X)) x
        = (toEuclideanLin (PUmat S)) ((toEuclideanLin X) x) := toEuclideanLin_mul_apply _ _ x
    have h1 : ‖(toEuclideanLin (PUmat S)) ((toEuclideanLin X) x)‖
        ≤ ‖(toEuclideanLin X) x‖ := norm_PU_le S _
    have h2 : ‖(toEuclideanLin X) x‖ ≤ spectralNorm X * ‖x‖ := norm_image_le X x
    have hgoal : ‖(toEuclideanLin (PUmat S * X)) x‖ ≤ spectralNorm X * ‖x‖ := by
      rw [happ]; exact le_trans h1 h2
    simpa [spectralNorm] using hgoal

/-- **dc89d139** tangent_projection_spectral_norm_le_universal_multiple, witness `C = 2`. -/
theorem tangentProjection_spectralNorm_le_two (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm (tangentProjection S X) ≤ 2 * spectralNorm X := by
  rw [tangentProjection_split]
  have htri : spectralNorm (PUmat S * X + (1 - PUmat S) * X * PVmat S)
      ≤ spectralNorm (PUmat S * X) + spectralNorm ((1 - PUmat S) * X * PVmat S) := by
    unfold spectralNorm
    rw [show toEuclideanLin (PUmat S * X + (1 - PUmat S) * X * PVmat S)
          = toEuclideanLin (PUmat S * X) + toEuclideanLin ((1 - PUmat S) * X * PVmat S) from
        map_add _ _ _]
    rw [show LinearMap.toContinuousLinearMap
            (toEuclideanLin (PUmat S * X) + toEuclideanLin ((1 - PUmat S) * X * PVmat S))
          = LinearMap.toContinuousLinearMap (toEuclideanLin (PUmat S * X))
            + LinearMap.toContinuousLinearMap (toEuclideanLin ((1 - PUmat S) * X * PVmat S)) from
        map_add _ _ _]
    exact norm_add_le _ _
  have hL : spectralNorm (PUmat S * X) ≤ spectralNorm X := norm_PU_mul_le S X
  have hR : spectralNorm ((1 - PUmat S) * X * PVmat S) ≤ spectralNorm X :=
    complLeft_times_spectralNorm_le S X (PVmat S) (fun x => norm_PV_le S x)
  linarith

end MatrixCompletion

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (normalProjection S X) ≤ spectralNorm X :=
  normalProjection_spectralNorm_le S X
