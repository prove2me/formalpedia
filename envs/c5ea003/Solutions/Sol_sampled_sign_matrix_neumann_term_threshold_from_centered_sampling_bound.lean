-- Prove2me | solution 1 for sampled_sign_matrix_neumann_term_threshold_from_centered_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T03:51:39.404867+00:00
-- url     : https://prove2.me/submissions/80abb0ac-1c19-49de-b18d-4819fa178791

import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped Classical BigOperators

namespace MatrixCompletion

open Matrix LinearMap Module InnerProductSpace WithLp

variable {n₁ n₂ r : Nat} {M : RealMatrix n₁ n₂}

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


-- ===== operator identity (certid) =====
theorem signMatrix_apply {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (i : Fin n1) (j : Fin n2) :
    signMatrix S i j = ∑ k : Fin r, S.u k i * S.v k j := by
  unfold signMatrix
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _
  rw [Matrix.vecMulVec_apply]

/-! ## Component: left projection fixes the sign matrix. -/

theorem leftSingularProjection_signMatrix {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) :
    leftSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  rw [signMatrix_apply]
  unfold leftSingularProjection
  -- ∑ a (∑ k u_k i u_k a) * (sign a j) = ∑ k u_k i v_k j
  -- rewrite sign a j
  rw [Finset.sum_congr rfl (fun a _ => by rw [signMatrix_apply S a j])]
  -- ∑ a (∑ k u_k i u_k a) * (∑ l u_l a v_l j) = ∑ k u_k i v_k j
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

/-! ## Component: right projection fixes the sign matrix. -/

theorem rightSingularProjection_signMatrix {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) :
    rightSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  rw [signMatrix_apply]
  unfold rightSingularProjection
  rw [Finset.sum_congr rfl (fun b _ => by rw [signMatrix_apply S i b])]
  -- ∑ b (∑ k u_k i v_k b) * (∑ l v_l b v_l j) = ∑ k u_k i v_k j
  have e1 : (∑ b : Fin n2, (∑ k : Fin r, S.u k i * S.v k b) * (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ b : Fin n2, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v k b) * (S.v l b * S.v l j) := by
    apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ b : Fin n2, ∑ l : Fin r, (S.u k i * S.v k b) * (S.v l b * S.v l j))
      = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n2, S.v k b * S.v l b) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n2, S.v k b * S.v l b))
      = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
    rw [S.v_orthonormal k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, S.u k i * S.v l j * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

/-! ## Component: two-sided projection fixes the sign matrix. -/

theorem twoSidedSingularProjection_signMatrix {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) :
    twoSidedSingularProjection S (signMatrix S) = signMatrix S := by
  -- twoSided(sign) = left(sign), then use the left lemma.
  refine Eq.trans ?_ (leftSingularProjection_signMatrix S)
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection
  -- LHS: ∑a ∑b (∑k u_k i u_k a) * (sign a b) * (∑l v_l b v_l j)
  -- RHS: ∑a (∑k u_k i u_k a) * (sign a j)
  apply Finset.sum_congr rfl; intro a _
  -- show ∑b (Pu_ia) * (sign a b) * (∑l v_l b v_l j) = Pu_ia * sign a j
  have hfac : (∑ b : Fin n2,
        (∑ k : Fin r, S.u k i * S.u k a) * signMatrix S a b * (∑ l : Fin r, S.v l b * S.v l j))
      = (∑ k : Fin r, S.u k i * S.u k a)
          * (∑ b : Fin n2, signMatrix S a b * (∑ l : Fin r, S.v l b * S.v l j)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  rw [hfac]
  -- Now show ∑b sign a b * (∑l v_l b v_l j) = sign a j  (this is right(sign) a j collapsed)
  congr 1
  -- ∑b (∑m u_m a v_m b) * (∑l v_l b v_l j) = ∑m u_m a v_m j   [= sign a j]
  rw [signMatrix_apply]
  conv_lhs => enter [2, b]; rw [signMatrix_apply S a b]
  -- ∑b (∑m u_m a v_m b)(∑l v_l b v_l j) = ∑m u_m a v_m j
  have e1 : (∑ b : Fin n2, (∑ m : Fin r, S.u m a * S.v m b) * (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ b : Fin n2, ∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (S.v m b * S.v l b) := by
    apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro l _; ring
  rw [e1, Finset.sum_comm]
  have e2 : (∑ m : Fin r, ∑ b : Fin n2, ∑ l : Fin r, (S.u m a * S.v l j) * (S.v m b * S.v l b))
      = ∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (∑ b : Fin n2, S.v m b * S.v l b) := by
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]
  rw [e2]
  have e3 : (∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (∑ b : Fin n2, S.v m b * S.v l b))
      = ∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (if m = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro l _
    rw [S.v_orthonormal m l]
  rw [e3]
  apply Finset.sum_congr rfl; intro m _
  have : (∑ l : Fin r, S.u m a * S.v l j * (if m = l then 1 else 0))
      = ∑ l : Fin r, (if m = l then S.u m a * S.v l j else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : m = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

/-! ## (1) tangent projection fixes the sign matrix. -/

theorem tangentProjection_signMatrix {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) :
    tangentProjection S (signMatrix S) = signMatrix S := by
  unfold tangentProjection
  rw [leftSingularProjection_signMatrix, rightSingularProjection_signMatrix,
    twoSidedSingularProjection_signMatrix]
  -- sign + sign - sign = sign
  abel

/-! ## Linearity of the projections (smul and sub). -/

theorem leftSingularProjection_smul {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    leftSingularProjection S (c • X) = c • leftSingularProjection S X := by
  funext i j
  unfold leftSingularProjection
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; ring

theorem rightSingularProjection_smul {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    rightSingularProjection S (c • X) = c • rightSingularProjection S X := by
  funext i j
  unfold rightSingularProjection
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem twoSidedSingularProjection_smul {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (c • X) = c • twoSidedSingularProjection S X := by
  funext i j
  unfold twoSidedSingularProjection
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _; ring

theorem tangentProjection_smul {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    tangentProjection S (c • X) = c • tangentProjection S X := by
  unfold tangentProjection
  rw [leftSingularProjection_smul, rightSingularProjection_smul, twoSidedSingularProjection_smul,
    smul_sub, smul_add]

theorem normalProjection_smul {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    normalProjection S (c • X) = c • normalProjection S X := by
  unfold normalProjection
  rw [tangentProjection_smul, smul_sub]

theorem leftSingularProjection_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    leftSingularProjection S (X - Y)
      = leftSingularProjection S X - leftSingularProjection S Y := by
  funext i j
  unfold leftSingularProjection
  rw [Matrix.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [Matrix.sub_apply]; ring

theorem rightSingularProjection_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    rightSingularProjection S (X - Y)
      = rightSingularProjection S X - rightSingularProjection S Y := by
  funext i j
  unfold rightSingularProjection
  rw [Matrix.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _
  rw [Matrix.sub_apply]; ring

theorem twoSidedSingularProjection_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    twoSidedSingularProjection S (X - Y)
      = twoSidedSingularProjection S X - twoSidedSingularProjection S Y := by
  funext i j
  unfold twoSidedSingularProjection
  rw [Matrix.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _
  rw [Matrix.sub_apply]; ring

theorem tangentProjection_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    tangentProjection S (X - Y) = tangentProjection S X - tangentProjection S Y := by
  unfold tangentProjection
  rw [leftSingularProjection_sub, rightSingularProjection_sub, twoSidedSingularProjection_sub]
  abel

theorem normalProjection_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    normalProjection S (X - Y) = normalProjection S X - normalProjection S Y := by
  unfold normalProjection
  rw [tangentProjection_sub]; abel

/-- The sign matrix is in the normal kernel: `P_{T^⊥}(sign) = 0`. -/
theorem normalProjection_signMatrix {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) :
    normalProjection S (signMatrix S) = 0 := by
  unfold normalProjection
  rw [tangentProjection_signMatrix]; abel

/-! ## (2) k=0 Neumann certificate term. -/

theorem neumannCertificateTerm_zero_eq {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : p ≠ 0) :
    neumannCertificateTerm Omega S p 0
      = normalProjection S (centeredSamplingFluctuation Omega p (signMatrix S)) := by
  unfold neumannCertificateTerm
  -- neumannIterate ... 0 = signMatrix S
  have hiter : neumannIterate Omega S p 0 = signMatrix S := by
    unfold neumannIterate; rw [Function.iterate_zero_apply]
  rw [hiter, tangentProjection_signMatrix]
  -- LHS = p⁻¹ • normalProjection S (samplingProjection Omega (signMatrix S))
  -- RHS unfolds centeredSamplingFluctuation
  unfold centeredSamplingFluctuation
  rw [normalProjection_smul, normalProjection_sub, normalProjection_smul,
    normalProjection_signMatrix, smul_zero, sub_zero]


-- ===== A1 entrySupNorm =====
theorem entrySupNorm_signMatrix_le_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu1 : ℝ) (h1 : A1 S mu1) (hn1 : 0 < n1) (hn2 : 0 < n2) :
    entrySupNorm (signMatrix S) ≤ mu1 * Real.sqrt ((r:ℝ) / ((n1:ℝ)*(n2:ℝ))) := by
  haveI : Nonempty (Fin n1) := ⟨⟨0, hn1⟩⟩
  haveI : Nonempty (Fin n2) := ⟨⟨0, hn2⟩⟩
  unfold entrySupNorm
  apply ciSup_le; intro i
  apply ciSup_le; intro j
  exact h1 i j


end MatrixCompletion

-- ===== pure-real envelope (top-level) =====
theorem d30_envelope
    (Cfixed beta lam mu1 K nn m rr : ℝ)
    (hCf : 0 ≤ Cfixed) (hb : 0 < beta) (hlam : 1 ≤ lam) (hmu1 : 1 ≤ mu1)
    (hK : 0 < K) (hlogK : 0 < Real.log K) (hnn : 0 < nn) (hm : 0 < m) (hr : 0 < rr)
    (hmbound : m ≥ lam * mu1^2 * K * rr * (beta * Real.log K)) :
    Cfixed * Real.sqrt ((beta * K * Real.log K) / (m / nn)) *
        (mu1 * Real.sqrt (rr / nn))
      ≤ Cfixed * Real.rpow lam (-(1/2)) := by
  have hlam_pos : 0 < lam := by linarith
  have hmu1_pos : 0 < mu1 := by linarith
  have hcombine : Real.sqrt ((beta * K * Real.log K) / (m / nn)) * Real.sqrt (rr / nn)
      = Real.sqrt ((beta * K * Real.log K * rr) / m) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    rw [div_div_eq_mul_div]
    field_simp
  have hlam_rpow : Real.rpow lam (-(1/2)) = (Real.sqrt lam)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hlam_pos.le]
    norm_num
  rw [show Cfixed * Real.sqrt ((beta * K * Real.log K) / (m / nn)) * (mu1 * Real.sqrt (rr / nn))
        = Cfixed * mu1 * (Real.sqrt ((beta * K * Real.log K) / (m / nn)) * Real.sqrt (rr / nn)) by ring,
     hcombine, hlam_rpow]
  -- goal: Cfixed * μ₁ * √((βKr logK)/m) ≤ Cfixed * (√lam)⁻¹
  have hslam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam_pos
  have hkey : mu1 * Real.sqrt ((beta * K * Real.log K * rr) / m) ≤ (Real.sqrt lam)⁻¹ := by
    rw [← Real.sqrt_mul_self hmu1_pos.le, ← Real.sqrt_mul (by positivity)]
    have hinv : (Real.sqrt lam)⁻¹ = Real.sqrt (1 / lam) := by
      rw [one_div, Real.sqrt_inv]
    rw [hinv]
    apply Real.sqrt_le_sqrt
    rw [show mu1 * mu1 * (beta * K * Real.log K * rr / m)
          = (mu1 * mu1 * (beta * K * Real.log K * rr)) / m by ring]
    rw [div_le_div_iff₀ hm hlam_pos]
    nlinarith [hmbound, sq_nonneg mu1]
  calc Cfixed * mu1 * Real.sqrt ((beta * K * Real.log K * rr) / m)
      = Cfixed * (mu1 * Real.sqrt ((beta * K * Real.log K * rr) / m)) := by ring
    _ ≤ Cfixed * (Real.sqrt lam)⁻¹ := mul_le_mul_of_nonneg_left hkey hCf

open MatrixCompletion

theorem solution (Cfixed : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (signMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (signMatrix S)) →
        NeumannCertificateTermSpectralBound Omega S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 0
          (C₀ * Real.rpow lam (-((1 : ℝ) / 2))) := by
  refine ⟨max Cfixed 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn1 hn2 hr hm hμ0 hμ1 hA0 hA1 hmbnd Omega hcsb
  -- abbreviations
  set K : ℝ := (↑(max n₁ n₂) : ℝ) with hKdef
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hpdef
  unfold NeumannCertificateTermSpectralBound
  unfold CenteredSamplingSpectralBound at hcsb
  have hC0pos : (0:ℝ) ≤ max Cfixed 1 := le_trans zero_le_one (le_max_right _ _)
  -- step A: operator identity + contraction
  have hRHS_nonneg : 0 ≤ (max Cfixed 1) * Real.rpow lam (-((1:ℝ)/2)) := by
    have : 0 ≤ Real.rpow lam (-((1:ℝ)/2)) := Real.rpow_nonneg (by linarith) _
    positivity
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0 ⟹ p = 0 ⟹ cert term 0 = 0
    have hp0 : p = 0 := by rw [hpdef, hm0]; simp
    have : neumannCertificateTerm Omega S p 0 = 0 := by
      unfold neumannCertificateTerm
      rw [hp0]; simp
    rw [this]
    have : spectralNorm (0 : RealMatrix n₁ n₂) = 0 := by
      unfold spectralNorm; simp
    rw [this]; exact hRHS_nonneg
  · have hmR_pos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hmpos
    have hnn_pos : (0:ℝ) < (n₁:ℝ)*(n₂:ℝ) := by positivity
    have hp_pos : 0 < p := by rw [hpdef]; positivity
    have hp_ne : p ≠ 0 := ne_of_gt hp_pos
    -- operator identity
    have hid : neumannCertificateTerm Omega S p 0
        = normalProjection S (centeredSamplingFluctuation Omega p (signMatrix S)) :=
      neumannCertificateTerm_zero_eq S Omega p hp_ne
    rw [hid]
    -- contraction
    have hcontr : spectralNorm (normalProjection S (centeredSamplingFluctuation Omega p (signMatrix S)))
        ≤ spectralNorm (centeredSamplingFluctuation Omega p (signMatrix S)) :=
      normal_spectral S _
    refine le_trans hcontr ?_
    -- hyp bound
    refine le_trans hcsb ?_
    -- bound: Cfixed * √(...) * entrySupNorm(sign) ≤ (max Cfixed 1) * lam^{-1/2}
    set sqterm : ℝ := Real.sqrt ((β * K * Real.log K) / p) with hsq
    have hsq_nonneg : 0 ≤ sqterm := Real.sqrt_nonneg _
    have hesn_nonneg : 0 ≤ entrySupNorm (signMatrix S) := by
      haveI : Nonempty (Fin n₁) := ⟨⟨0, hn1⟩⟩
      haveI : Nonempty (Fin n₂) := ⟨⟨0, hn2⟩⟩
      unfold entrySupNorm
      refine le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, hn1⟩ ?_
      refine le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, hn2⟩ ?_
      exact abs_nonneg _
    -- Cfixed * sq * esn ≤ (max Cfixed 1) * sq * esn
    have hstep1 : Cfixed * sqterm * entrySupNorm (signMatrix S)
        ≤ (max Cfixed 1) * sqterm * entrySupNorm (signMatrix S) := by
      apply mul_le_mul_of_nonneg_right _ hesn_nonneg
      apply mul_le_mul_of_nonneg_right (le_max_left _ _) hsq_nonneg
    refine le_trans hstep1 ?_
    -- esn ≤ μ₁ √(r/(n₁n₂))
    have hesn_le : entrySupNorm (signMatrix S) ≤ μ₁ * Real.sqrt ((r:ℝ)/((n₁:ℝ)*(n₂:ℝ))) :=
      entrySupNorm_signMatrix_le_A1 S μ₁ hA1 hn1 hn2
    have hstep2 : (max Cfixed 1) * sqterm * entrySupNorm (signMatrix S)
        ≤ (max Cfixed 1) * sqterm * (μ₁ * Real.sqrt ((r:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left hesn_le
      apply mul_nonneg hC0pos hsq_nonneg
    refine le_trans hstep2 ?_
    -- case on max n₁ n₂
    rcases Nat.lt_or_ge (max n₁ n₂) 2 with hmaxlt | hmaxge
    · -- max = 1: K = 1, logK = 0, sqterm = 0 ⟹ whole bound 0
      have hmax1 : max n₁ n₂ = 1 := by have := Nat.le_max_left n₁ n₂; omega
      have hK1 : K = 1 := by rw [hKdef, hmax1]; norm_num
      have hsq0 : sqterm = 0 := by
        rw [hsq, hK1]
        simp [Real.log_one]
      rw [hsq0]
      rw [mul_zero, zero_mul]
      exact hRHS_nonneg
    · -- max ≥ 2: apply envelope
      have hK2 : (2:ℝ) ≤ K := by rw [hKdef]; exact_mod_cast hmaxge
      have hlogK_pos : 0 < Real.log K := Real.log_pos (by linarith)
      have hrR_pos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
      have henv := d30_envelope (max Cfixed 1) β lam μ₁ K ((n₁:ℝ)*(n₂:ℝ)) (m:ℝ) (r:ℝ)
        hC0pos (by linarith) hlam (by linarith) (by linarith) hlogK_pos
        hnn_pos hmR_pos hrR_pos ?_
      · rw [hsq, hpdef]
        convert henv using 2
      · rw [hKdef]; exact hmbnd
