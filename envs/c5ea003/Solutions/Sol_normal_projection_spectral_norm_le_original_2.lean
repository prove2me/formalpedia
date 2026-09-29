-- Prove2me | solution 2 for normal_projection_spectral_norm_le_original
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T02:41:56.356236+00:00
-- url     : https://prove2.me/submissions/9b085e95-ff79-4e95-9d17-1ee674c7d214

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic

open scoped Classical BigOperators

namespace MatrixCompletion

open Matrix LinearMap Module InnerProductSpace WithLp

variable {n₁ n₂ r : Nat} {M : RealMatrix n₁ n₂}

/-! ## ker_idem (orthonormality) -/

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

/-! ## Projector matrices PU, PV and factorizations. -/

noncomputable def PUmat (S : SVD M r) : Matrix (Fin n₁) (Fin n₁) ℝ :=
  fun i a => ∑ k : Fin r, S.u k i * S.u k a

noncomputable def PVmat (S : SVD M r) : Matrix (Fin n₂) (Fin n₂) ℝ :=
  fun b j => ∑ k : Fin r, S.v k b * S.v k j

theorem PUmat_apply (S : SVD M r) (i a : Fin n₁) :
    PUmat S i a = ∑ k, S.u k i * S.u k a := rfl

theorem PVmat_apply (S : SVD M r) (b j : Fin n₂) :
    PVmat S b j = ∑ k, S.v k b * S.v k j := rfl

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
  have hrew : ∀ b : Fin n₂, (PUmat S * X) i b * PVmat S b j
      = (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * X a b)
          * (∑ l : Fin r, S.v l b * S.v l j) := by
    intro b
    rw [Matrix.mul_apply, PVmat_apply]
    simp only [PUmat_apply]
  rw [Finset.sum_congr rfl (fun b _ => hrew b)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

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

theorem normalProjection_factor (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    normalProjection S Z = (1 - PUmat S) * Z * (1 - PVmat S) := by
  unfold normalProjection tangentProjection
  rw [left_eq_PU, right_eq_PV, two_eq_PU_PV]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  abel

theorem PU_symm (S : SVD M r) : (PUmat S)ᵀ = PUmat S := by
  funext i j
  rw [Matrix.transpose_apply, PUmat_apply, PUmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

theorem PV_symm (S : SVD M r) : (PVmat S)ᵀ = PVmat S := by
  funext i j
  rw [Matrix.transpose_apply, PVmat_apply, PVmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

/-! ## Analytic toolkit (harvested from Nopb). -/

theorem ofLp_image (A : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    ofLp ((toEuclideanLin A) x) = A *ᵥ ofLp x :=
  Matrix.ofLp_toEuclideanLin_apply A x

theorem eucl_inner_eq_sum {N : ℕ} (a b : EuclideanSpace ℝ (Fin N)) :
    (inner ℝ a b : ℝ) = ∑ i, (ofLp a) i * (ofLp b) i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl; intro i _
  rw [show (⟪a i, b i⟫_ℝ : ℝ) = b i * (starRingEnd ℝ) (a i) from RCLike.inner_apply _ _,
      conj_trivial]; ring

theorem normSq_eq_sum {N : ℕ} (a : EuclideanSpace ℝ (Fin N)) :
    ‖a‖ ^ 2 = ∑ i, (ofLp a) i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, eucl_inner_eq_sum]
  apply Finset.sum_congr rfl; intro i _; ring

theorem mulVec_dot_eq_transpose_mul (B C : RealMatrix n₁ n₂) (x : Fin n₂ → ℝ) :
    (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ p, ∑ q, (Bᵀ * C) p q * x p * x q := by
  have e1 : (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ i, (∑ p, B i p * x p) * (∑ q, C i q * x q) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.mulVec, Matrix.mulVec]; rfl
  rw [e1]
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

theorem normSq_image_eq_quad (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ^ 2
      = ∑ p, ∑ q, (Bᵀ * B) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  have : (∑ i, (ofLp ((toEuclideanLin B) y)) i ^ 2)
      = ∑ i, (B *ᵥ ofLp y) i * (B *ᵥ ofLp y) i := by
    apply Finset.sum_congr rfl; intro i _; rw [ofLp_image]; ring
  rw [this, mulVec_dot_eq_transpose_mul]

theorem normSq_eq_one_quad {N : ℕ} (y : EuclideanSpace ℝ (Fin N)) :
    ‖y‖ ^ 2 = ∑ p, ∑ q, (1 : Matrix (Fin N) (Fin N) ℝ) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq]; ring
  · intro q _ hq; rw [Matrix.one_apply_ne (Ne.symm hq)]; ring
  · intro h; exact absurd (Finset.mem_univ p) h

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

theorem norm_image_le (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ≤ spectralNorm B * ‖y‖ := by
  unfold spectralNorm
  have h := (LinearMap.toContinuousLinearMap (toEuclideanLin B)).le_opNorm y
  simpa using h

/-- Orthogonal projection `P` (symmetric idempotent) is a contraction. -/
theorem norm_proj_le {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin P) y‖ ≤ ‖y‖ := by
  have hsplit := pythagoras_split P hsymm hidem y
  have hle : ‖(toEuclideanLin P) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(toEuclideanLin (1 - P)) y‖]
  nlinarith [hle, norm_nonneg ((toEuclideanLin P) y), norm_nonneg y]

theorem norm_compl_le {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin (1 - P)) y‖ ≤ ‖y‖ := by
  have hsplit := pythagoras_split P hsymm hidem y
  have hle : ‖(toEuclideanLin (1 - P)) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(toEuclideanLin P) y‖]
  nlinarith [hle, norm_nonneg ((toEuclideanLin (1 - P)) y), norm_nonneg y]

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

/-! ## spectralNorm bound via per-vector estimate. -/

theorem spectralNorm_nonneg (X : RealMatrix n₁ n₂) : 0 ≤ spectralNorm X := by
  unfold spectralNorm; exact norm_nonneg _

/-- If `‖(toEuclideanLin Y) v‖ ≤ b * ‖v‖` for all v with 0≤b, then spectralNorm Y ≤ b. -/
theorem spectralNorm_le_of_bound (Y : RealMatrix n₁ n₂) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ v : EuclideanSpace ℝ (Fin n₂), ‖(toEuclideanLin Y) v‖ ≤ b * ‖v‖) :
    spectralNorm Y ≤ b := by
  unfold spectralNorm
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro v
  simpa using h v

/-! ## The 4 spectral-norm projection nodes. -/

/-- normal_projection_spectral_norm_le_original. -/
theorem normal_spectral (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm (normalProjection S X) ≤ spectralNorm X := by
  apply spectralNorm_le_of_bound _ _ (spectralNorm_nonneg X)
  intro v
  rw [normalProjection_factor S X]
  -- (1-PU)*X*(1-PV) v = (1-PU)(X((1-PV)v))
  rw [show (1 - PUmat S) * X * (1 - PVmat S) = (1 - PUmat S) * (X * (1 - PVmat S)) from by
        rw [Matrix.mul_assoc]]
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
  calc ‖(toEuclideanLin (1 - PUmat S)) ((toEuclideanLin X) ((toEuclideanLin (1 - PVmat S)) v))‖
      ≤ ‖(toEuclideanLin X) ((toEuclideanLin (1 - PVmat S)) v)‖ :=
        norm_compl_le (PUmat S) (PU_symm S) (PU_idem S) _
    _ ≤ spectralNorm X * ‖(toEuclideanLin (1 - PVmat S)) v‖ := norm_image_le X _
    _ ≤ spectralNorm X * ‖v‖ := by
        apply mul_le_mul_of_nonneg_left (norm_compl_le (PVmat S) (PV_symm S) (PV_idem S) v)
          (spectralNorm_nonneg X)

/-- singular_projection_inclusion_exclusion_spectral_norm_le_original. -/
theorem incl_excl_spectral (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm
        (X - leftSingularProjection S X - rightSingularProjection S X +
          twoSidedSingularProjection S X) ≤ spectralNorm X := by
  have heq : (X - leftSingularProjection S X - rightSingularProjection S X +
        twoSidedSingularProjection S X) = normalProjection S X := by
    unfold normalProjection tangentProjection
    abel
  rw [heq]
  exact normal_spectral S X

/-- right_singular_projection_minus_two_sided_spectral_norm_le_original. -/
theorem right_minus_two_spectral (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm (rightSingularProjection S X - twoSidedSingularProjection S X) ≤
      spectralNorm X := by
  apply spectralNorm_le_of_bound _ _ (spectralNorm_nonneg X)
  intro v
  -- R - T2 = X*PV - PU*X*PV = (1-PU)*X*PV
  have hfac : rightSingularProjection S X - twoSidedSingularProjection S X
      = (1 - PUmat S) * (X * PVmat S) := by
    rw [right_eq_PV S X, two_eq_PU_PV S X]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [hfac, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
  calc ‖(toEuclideanLin (1 - PUmat S)) ((toEuclideanLin X) ((toEuclideanLin (PVmat S)) v))‖
      ≤ ‖(toEuclideanLin X) ((toEuclideanLin (PVmat S)) v)‖ :=
        norm_compl_le (PUmat S) (PU_symm S) (PU_idem S) _
    _ ≤ spectralNorm X * ‖(toEuclideanLin (PVmat S)) v‖ := norm_image_le X _
    _ ≤ spectralNorm X * ‖v‖ := by
        apply mul_le_mul_of_nonneg_left (norm_proj_le (PVmat S) (PV_symm S) (PV_idem S) v)
          (spectralNorm_nonneg X)

theorem tangent_decomp (S : SVD M r) (X : RealMatrix n₁ n₂) :
    tangentProjection S X
      = leftSingularProjection S X + rightSingularProjection S X
        - twoSidedSingularProjection S X := rfl

/-- Left projection contraction (needed for the tangent triangle bound). -/
theorem left_spectral (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm (leftSingularProjection S X) ≤ spectralNorm X := by
  apply spectralNorm_le_of_bound _ _ (spectralNorm_nonneg X)
  intro v
  rw [left_eq_PU S X, toEuclideanLin_mul_apply]
  calc ‖(toEuclideanLin (PUmat S)) ((toEuclideanLin X) v)‖
      ≤ ‖(toEuclideanLin X) v‖ := norm_proj_le (PUmat S) (PU_symm S) (PU_idem S) _
    _ ≤ spectralNorm X * ‖v‖ := norm_image_le X v

/-- Right projection contraction. -/
theorem right_spectral (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm (rightSingularProjection S X) ≤ spectralNorm X := by
  apply spectralNorm_le_of_bound _ _ (spectralNorm_nonneg X)
  intro v
  rw [right_eq_PV S X, toEuclideanLin_mul_apply]
  calc ‖(toEuclideanLin X) ((toEuclideanLin (PVmat S)) v)‖
      ≤ spectralNorm X * ‖(toEuclideanLin (PVmat S)) v‖ := norm_image_le X _
    _ ≤ spectralNorm X * ‖v‖ := by
        apply mul_le_mul_of_nonneg_left (norm_proj_le (PVmat S) (PV_symm S) (PV_idem S) v)
          (spectralNorm_nonneg X)

/-- Two-sided projection contraction. -/
theorem two_spectral (S : SVD M r) (X : RealMatrix n₁ n₂) :
    spectralNorm (twoSidedSingularProjection S X) ≤ spectralNorm X := by
  apply spectralNorm_le_of_bound _ _ (spectralNorm_nonneg X)
  intro v
  rw [two_eq_PU_PV S X]
  rw [show PUmat S * X * PVmat S = PUmat S * (X * PVmat S) from by rw [Matrix.mul_assoc]]
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
  calc ‖(toEuclideanLin (PUmat S)) ((toEuclideanLin X) ((toEuclideanLin (PVmat S)) v))‖
      ≤ ‖(toEuclideanLin X) ((toEuclideanLin (PVmat S)) v)‖ :=
        norm_proj_le (PUmat S) (PU_symm S) (PU_idem S) _
    _ ≤ spectralNorm X * ‖(toEuclideanLin (PVmat S)) v‖ := norm_image_le X _
    _ ≤ spectralNorm X * ‖v‖ := by
        apply mul_le_mul_of_nonneg_left (norm_proj_le (PVmat S) (PV_symm S) (PV_idem S) v)
          (spectralNorm_nonneg X)

/-- spectralNorm triangle inequality (subadditivity). -/
theorem spectralNorm_add_le (A B : RealMatrix n₁ n₂) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  unfold spectralNorm
  rw [show LinearMap.toContinuousLinearMap (toEuclideanLin (A + B))
        = LinearMap.toContinuousLinearMap (toEuclideanLin A)
          + LinearMap.toContinuousLinearMap (toEuclideanLin B) from by
        refine ContinuousLinearMap.ext (fun v => ?_)
        rw [ContinuousLinearMap.add_apply]
        simp only [LinearMap.coe_toContinuousLinearMap']
        exact toEuclideanLin_add_apply A B v]
  exact norm_add_le _ _

theorem toEuclideanLin_neg_apply (B : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (-B)) x = -((toEuclideanLin B) x) := by
  apply ofLp_injective
  rw [ofLp_image]
  rw [show ofLp (-((toEuclideanLin B) x)) = -(ofLp ((toEuclideanLin B) x)) from rfl]
  rw [ofLp_image, Matrix.neg_mulVec]

theorem spectralNorm_neg (B : RealMatrix n₁ n₂) :
    spectralNorm (-B) = spectralNorm B := by
  unfold spectralNorm
  rw [show LinearMap.toContinuousLinearMap (toEuclideanLin (-B))
        = -(LinearMap.toContinuousLinearMap (toEuclideanLin B)) from by
        refine ContinuousLinearMap.ext (fun v => ?_)
        rw [ContinuousLinearMap.neg_apply]
        simp only [LinearMap.coe_toContinuousLinearMap']
        exact toEuclideanLin_neg_apply B v]
  rw [norm_neg]

theorem spectralNorm_sub_le (A B : RealMatrix n₁ n₂) :
    spectralNorm (A - B) ≤ spectralNorm A + spectralNorm B := by
  rw [show A - B = A + (-B) from by abel]
  refine le_trans (spectralNorm_add_le A (-B)) ?_
  rw [spectralNorm_neg]

end MatrixCompletion

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (normalProjection S X) ≤ spectralNorm X :=
  MatrixCompletion.normal_spectral S X
