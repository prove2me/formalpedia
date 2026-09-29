-- Prove2me | solution 1 for neumann_scaled_contraction_and_sampled_frobenius_imply_remainder_formula_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T04:25:06.707111+00:00
-- url     : https://prove2.me/submissions/c90be819-8598-4115-a0ac-c374586163f9

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

/-! ## spectralNorm machinery (copied from Scratch_spectral / Scratch_smul). -/

theorem spectralNorm_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) : 0 ≤ spectralNorm X := by
  unfold spectralNorm; exact norm_nonneg _

theorem spectralNorm_smul {n1 n2 : Nat} (c : ℝ) (X : RealMatrix n1 n2) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  have h1 : (Matrix.toEuclideanLin (c • X)) = c • (Matrix.toEuclideanLin X) := by
    apply LinearMap.map_smul
  rw [h1, map_smul, norm_smul]
  simp [Real.norm_eq_abs]

theorem toEuclideanLin_add_apply {n1 n2 : Nat} (A B : RealMatrix n1 n2)
    (x : EuclideanSpace ℝ (Fin n2)) :
    (toEuclideanLin (A + B)) x = (toEuclideanLin A) x + (toEuclideanLin B) x := by
  apply ofLp_injective
  rw [Matrix.ofLp_toEuclideanLin_apply]
  rw [show ofLp ((toEuclideanLin A) x + (toEuclideanLin B) x)
        = ofLp ((toEuclideanLin A) x) + ofLp ((toEuclideanLin B) x) from rfl]
  rw [Matrix.ofLp_toEuclideanLin_apply, Matrix.ofLp_toEuclideanLin_apply, Matrix.add_mulVec]

theorem spectralNorm_add_le {n1 n2 : Nat} (A B : RealMatrix n1 n2) :
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

theorem spectralNorm_zero {n1 n2 : Nat} : spectralNorm (0 : RealMatrix n1 n2) = 0 := by
  unfold spectralNorm
  rw [show (Matrix.toEuclideanLin (0 : RealMatrix n1 n2)) = 0 from by
        apply LinearMap.ext; intro v; simp]
  simp

/-- spectralNorm of a finite sum ≤ sum of spectralNorms (triangle for sums). -/
theorem spectralNorm_sum_le {n1 n2 : Nat} {ι : Type*} (s : Finset ι)
    (f : ι → RealMatrix n1 n2) :
    spectralNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, spectralNorm (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; rw [spectralNorm_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine le_trans (spectralNorm_add_le _ _) ?_
      linarith [ih]

/-! ## frobeniusNorm machinery. -/

theorem spectralNorm_le_frobeniusNorm {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    spectralNorm X ≤ frobeniusNorm X := by
  unfold spectralNorm
  have hfro_nonneg : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hfro_nonneg ?_
  intro v
  rw [LinearMap.coe_toContinuousLinearMap']
  have hv_normsq : ‖v‖ ^ 2 = ∑ j : Fin n2, (v j) ^ 2 := EuclideanSpace.real_norm_sq_eq v
  have hfv_normsq : ‖(Matrix.toEuclideanLin X) v‖ ^ 2 =
      ∑ i : Fin n1, ((Matrix.toEuclideanLin X) v i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq _
  have hentry : ∀ i : Fin n1, (Matrix.toEuclideanLin X) v i = ∑ j : Fin n2, X i j * v j := by
    intro i; rfl
  rw [frobeniusNorm]
  have hnormv_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  have hfvnonneg : 0 ≤ ‖(Matrix.toEuclideanLin X) v‖ := norm_nonneg _
  have hrhs : Real.sqrt (frobeniusNormSq X) * ‖v‖
      = Real.sqrt (frobeniusNormSq X * (∑ j : Fin n2, (v j) ^ 2)) := by
    rw [Real.sqrt_mul (by unfold frobeniusNormSq; positivity)]
    congr 1
    rw [← hv_normsq, Real.sqrt_sq hnormv_nonneg]
  rw [hrhs]
  rw [show ‖(Matrix.toEuclideanLin X) v‖ = Real.sqrt (‖(Matrix.toEuclideanLin X) v‖ ^ 2) from
    (Real.sqrt_sq hfvnonneg).symm]
  apply Real.sqrt_le_sqrt
  rw [hfv_normsq]
  calc ∑ i : Fin n1, ((Matrix.toEuclideanLin X) v i) ^ 2
      = ∑ i : Fin n1, (∑ j : Fin n2, X i j * v j) ^ 2 := by
        apply Finset.sum_congr rfl; intro i _; rw [hentry i]
    _ ≤ ∑ i : Fin n1, ((∑ j : Fin n2, (X i j) ^ 2) * (∑ j : Fin n2, (v j) ^ 2)) := by
        apply Finset.sum_le_sum; intro i _
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => X i j) (fun j => v j)
    _ = (∑ i : Fin n1, ∑ j : Fin n2, (X i j) ^ 2) * (∑ j : Fin n2, (v j) ^ 2) := by
        rw [← Finset.sum_mul]
    _ = frobeniusNormSq X * (∑ j : Fin n2, (v j) ^ 2) := by rw [frobeniusNormSq]

theorem frobeniusNorm_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ frobeniusNorm X := Real.sqrt_nonneg _

theorem frobeniusNormSq_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ frobeniusNormSq X := by unfold frobeniusNormSq; positivity

/-! ## Projector matrices PU, PV (copied from Scratch_spectral). -/

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

variable {n₁ n₂ r : Nat} {M : RealMatrix n₁ n₂}

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

/-! ## Frobenius contraction under left/right multiplication by a projector. -/

/-- For a symmetric idempotent matrix `P` and any vector `y`,
`‖(toEuclideanLin P) y‖ ≤ ‖y‖`.  (We reprove the pieces inline.) -/
theorem normSq_eq_sum {N : ℕ} (a : EuclideanSpace ℝ (Fin N)) :
    ‖a‖ ^ 2 = ∑ i, (ofLp a) i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl; intro i _
  rw [show (⟪a i, a i⟫_ℝ : ℝ) = a i * (starRingEnd ℝ) (a i) from RCLike.inner_apply _ _,
      conj_trivial]; ring

theorem ofLp_image (A : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    ofLp ((toEuclideanLin A) x) = A *ᵥ ofLp x :=
  Matrix.ofLp_toEuclideanLin_apply A x

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

/-- Frobenius norm squared expressed column-by-column. -/
theorem frobeniusNormSq_eq_col_sum {a b : Nat} (Z : RealMatrix a b) :
    frobeniusNormSq Z = ∑ j : Fin b, ∑ i : Fin a, (Z i j) ^ 2 := by
  unfold frobeniusNormSq
  rw [Finset.sum_comm]

/-- Left multiplication by a symmetric idempotent (projector) is a Frobenius contraction. -/
theorem frobeniusNormSq_proj_mul_le {a c : Nat} (P : Matrix (Fin a) (Fin a) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (Z : RealMatrix a c) :
    frobeniusNormSq (P * Z) ≤ frobeniusNormSq Z := by
  rw [frobeniusNormSq_eq_col_sum, frobeniusNormSq_eq_col_sum]
  apply Finset.sum_le_sum
  intro j _
  -- column j as a EuclideanSpace vector
  set col : EuclideanSpace ℝ (Fin a) := (WithLp.toLp 2 (fun i => Z i j)) with hcol
  have hcolentry : ∀ i, ofLp col i = Z i j := by intro i; rfl
  -- ∑ i ((P*Z) i j)^2 = ‖(toEuclideanLin P) col‖^2
  have hPZ : ∀ i, (P * Z) i j = (toEuclideanLin P) col i := by
    intro i
    have heq : (toEuclideanLin P) col i = (P *ᵥ ofLp col) i := by
      rw [← ofLp_image]
    rw [heq, Matrix.mulVec, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro k _
    rw [hcolentry]
  have hlhs : (∑ i : Fin a, ((P * Z) i j) ^ 2) = ‖(toEuclideanLin P) col‖ ^ 2 := by
    rw [normSq_eq_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [hPZ i]
  have hrhs : (∑ i : Fin a, (Z i j) ^ 2) = ‖col‖ ^ 2 := by
    rw [normSq_eq_sum]
  rw [hlhs, hrhs]
  have hnn1 : 0 ≤ ‖(toEuclideanLin P) col‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖col‖ := norm_nonneg _
  have := norm_proj_le P hsymm hidem col
  nlinarith [this, hnn1, hnn2]

/-- Right multiplication by a symmetric idempotent is a Frobenius contraction. -/
theorem frobeniusNormSq_mul_proj_le {a c : Nat} (Q : Matrix (Fin c) (Fin c) ℝ)
    (hsymm : Qᵀ = Q) (hidem : Q * Q = Q) (Z : RealMatrix a c) :
    frobeniusNormSq (Z * Q) ≤ frobeniusNormSq Z := by
  -- transpose to reduce to the left case
  have htrans : ∀ (W : RealMatrix a c), frobeniusNormSq W = frobeniusNormSq Wᵀ := by
    intro W
    unfold frobeniusNormSq
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.transpose_apply]
  rw [htrans (Z * Q), Matrix.transpose_mul, htrans Z]
  -- Qᵀ * Zᵀ, Qᵀ is symmetric idempotent
  have hsymmT : (Qᵀ)ᵀ = Qᵀ := by rw [Matrix.transpose_transpose, hsymm]
  have hidemT : Qᵀ * Qᵀ = Qᵀ := by rw [← Matrix.transpose_mul, hidem]
  exact frobeniusNormSq_proj_mul_le Qᵀ hsymmT hidemT Zᵀ

/-- The key STEP-3 lemma: the normal projection is a Frobenius contraction. -/
theorem frobeniusNorm_normalProjection_le (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    frobeniusNorm (normalProjection S Z) ≤ frobeniusNorm Z := by
  rw [normalProjection_factor S Z]
  -- (1-PU) symmetric idempotent; (1-PV) symmetric idempotent
  have hPUs : ((1 : Matrix (Fin n₁) (Fin n₁) ℝ) - PUmat S)ᵀ = (1 - PUmat S) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, PU_symm]
  have hPUi : ((1 : Matrix (Fin n₁) (Fin n₁) ℝ) - PUmat S) * (1 - PUmat S) = 1 - PUmat S := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, PU_idem]; abel
  have hPVs : ((1 : Matrix (Fin n₂) (Fin n₂) ℝ) - PVmat S)ᵀ = (1 - PVmat S) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, PV_symm]
  have hPVi : ((1 : Matrix (Fin n₂) (Fin n₂) ℝ) - PVmat S) * (1 - PVmat S) = 1 - PVmat S := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, PV_idem]; abel
  unfold frobeniusNorm
  apply Real.sqrt_le_sqrt
  calc frobeniusNormSq ((1 - PUmat S) * Z * (1 - PVmat S))
      ≤ frobeniusNormSq ((1 - PUmat S) * Z) :=
        frobeniusNormSq_mul_proj_le (1 - PVmat S) hPVs hPVi ((1 - PUmat S) * Z)
    _ ≤ frobeniusNormSq Z := frobeniusNormSq_proj_mul_le (1 - PUmat S) hPUs hPUi Z

/-! ## Tangent projection: idempotence + linearity + sign-fixedness. -/

theorem tangentProjection_as_matrix (S : SVD M r) (X : RealMatrix n₁ n₂) :
    tangentProjection S X = PUmat S * X + X * PVmat S - PUmat S * X * PVmat S := by
  unfold tangentProjection
  rw [left_eq_PU, right_eq_PV, two_eq_PU_PV]

theorem tangentProjection_idem (S : SVD M r) (X : RealMatrix n₁ n₂) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  rw [tangentProjection_as_matrix S (tangentProjection S X), tangentProjection_as_matrix S X]
  set A := PUmat S * X + X * PVmat S - PUmat S * X * PVmat S with hA
  have hPP : PUmat S * PUmat S = PUmat S := PU_idem S
  have hQQ : PVmat S * PVmat S = PVmat S := PV_idem S
  -- PU * A = PU X
  have hPUA : PUmat S * A = PUmat S * X := by
    rw [hA, Matrix.mul_sub, Matrix.mul_add]
    rw [show PUmat S * (PUmat S * X) = (PUmat S * PUmat S) * X from
          (Matrix.mul_assoc _ _ _).symm, hPP]
    rw [show PUmat S * (PUmat S * X * PVmat S)
          = (PUmat S * PUmat S) * X * PVmat S from by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (PUmat S) (PUmat S)], hPP]
    -- PU X + (PU X) PV - (PU X) PV = PU X  (note PU*(X*PV) = (PU*X)*PV)
    rw [show PUmat S * (X * PVmat S) = PUmat S * X * PVmat S from (Matrix.mul_assoc _ _ _).symm]
    abel
  -- A * PV = X PV
  have hAPV : A * PVmat S = X * PVmat S := by
    rw [hA, Matrix.sub_mul, Matrix.add_mul]
    rw [show X * PVmat S * PVmat S = X * (PVmat S * PVmat S) from Matrix.mul_assoc _ _ _, hQQ]
    rw [show PUmat S * X * PVmat S * PVmat S = PUmat S * X * (PVmat S * PVmat S) from
          Matrix.mul_assoc _ _ _, hQQ]
    -- (PU X) PV + X PV - (PU X) PV = X PV
    abel
  -- goal: PU*A + A*PV - PU*A*PV = A.  rw hPUA (both PU*A occurrences) and hAPV.
  rw [hPUA, hAPV, hA]

theorem tangentProjection_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n₁ n₂) :
    tangentProjection S (c • X) = c • tangentProjection S X := by
  rw [tangentProjection_as_matrix S (c • X), tangentProjection_as_matrix S X]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]

theorem tangentProjection_sub (S : SVD M r) (X Y : RealMatrix n₁ n₂) :
    tangentProjection S (X - Y) = tangentProjection S X - tangentProjection S Y := by
  rw [tangentProjection_as_matrix S (X - Y), tangentProjection_as_matrix S X,
    tangentProjection_as_matrix S Y]
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- The error operator output is in the tangent space (STEP 1). -/
theorem tangentProjection_neumannErrorOperator (S : SVD M r)
    (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) (X : RealMatrix n₁ n₂) :
    tangentProjection S (neumannErrorOperator Omega S p X) = neumannErrorOperator Omega S p X := by
  unfold neumannErrorOperator
  rw [tangentProjection_sub, tangentProjection_smul, tangentProjection_idem,
    tangentProjection_idem]

/-! ## Sign matrix is tangent-fixed (copied from Scratch_certid). -/

theorem signMatrix_apply' (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    signMatrix S i j = ∑ k : Fin r, S.u k i * S.v k j := by
  unfold signMatrix
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _
  rw [Matrix.vecMulVec_apply]

theorem leftSingularProjection_signMatrix (S : SVD M r) :
    leftSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  rw [signMatrix_apply']
  unfold leftSingularProjection
  rw [Finset.sum_congr rfl (fun a _ => by rw [signMatrix_apply' S a j])]
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

theorem rightSingularProjection_signMatrix (S : SVD M r) :
    rightSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  rw [signMatrix_apply']
  unfold rightSingularProjection
  rw [Finset.sum_congr rfl (fun b _ => by rw [signMatrix_apply' S i b])]
  have e1 : (∑ b : Fin n₂, (∑ k : Fin r, S.u k i * S.v k b) * (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ b : Fin n₂, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v k b) * (S.v l b * S.v l j) := by
    apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ b : Fin n₂, ∑ l : Fin r, (S.u k i * S.v k b) * (S.v l b * S.v l j))
      = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n₂, S.v k b * S.v l b) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n₂, S.v k b * S.v l b))
      = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
    rw [S.v_orthonormal k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, S.u k i * S.v l j * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

theorem twoSidedSingularProjection_signMatrix (S : SVD M r) :
    twoSidedSingularProjection S (signMatrix S) = signMatrix S := by
  refine Eq.trans ?_ (leftSingularProjection_signMatrix S)
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection
  apply Finset.sum_congr rfl; intro a _
  have hfac : (∑ b : Fin n₂,
        (∑ k : Fin r, S.u k i * S.u k a) * signMatrix S a b * (∑ l : Fin r, S.v l b * S.v l j))
      = (∑ k : Fin r, S.u k i * S.u k a)
          * (∑ b : Fin n₂, signMatrix S a b * (∑ l : Fin r, S.v l b * S.v l j)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  rw [hfac]
  congr 1
  rw [signMatrix_apply']
  conv_lhs => enter [2, b]; rw [signMatrix_apply' S a b]
  have e1 : (∑ b : Fin n₂, (∑ m : Fin r, S.u m a * S.v m b) * (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ b : Fin n₂, ∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (S.v m b * S.v l b) := by
    apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro l _; ring
  rw [e1, Finset.sum_comm]
  have e2 : (∑ m : Fin r, ∑ b : Fin n₂, ∑ l : Fin r, (S.u m a * S.v l j) * (S.v m b * S.v l b))
      = ∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (∑ b : Fin n₂, S.v m b * S.v l b) := by
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]
  rw [e2]
  have e3 : (∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (∑ b : Fin n₂, S.v m b * S.v l b))
      = ∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (if m = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro l _
    rw [S.v_orthonormal m l]
  rw [e3]
  apply Finset.sum_congr rfl; intro m _
  have : (∑ l : Fin r, S.u m a * S.v l j * (if m = l then 1 else 0))
      = ∑ l : Fin r, (if m = l then S.u m a * S.v l j else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : m = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

theorem tangentProjection_signMatrix (S : SVD M r) :
    tangentProjection S (signMatrix S) = signMatrix S := by
  unfold tangentProjection
  rw [leftSingularProjection_signMatrix, rightSingularProjection_signMatrix,
    twoSidedSingularProjection_signMatrix]
  abel

/-! ## STEP 2: iterate Frobenius bound + tangent-fixedness of iterates. -/

theorem neumannIterate_tangent_fixed (S : SVD M r)
    (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) (k : ℕ) :
    tangentProjection S (neumannIterate Omega S p k) = neumannIterate Omega S p k := by
  cases k with
  | zero =>
      unfold neumannIterate
      rw [Function.iterate_zero_apply]
      exact tangentProjection_signMatrix S
  | succ n =>
      unfold neumannIterate
      rw [Function.iterate_succ_apply']
      exact tangentProjection_neumannErrorOperator S Omega p _

theorem neumannIterate_frobenius_bound (S : SVD M r)
    (Omega : Finset (Fin n₁ × Fin n₂)) (p ρ' : ℝ)
    (hρ'0 : 0 ≤ ρ')
    (hcontr : ∀ X : RealMatrix n₁ n₂, tangentProjection S X = X →
        frobeniusNorm (neumannErrorOperator Omega S p X) ≤ ρ' * frobeniusNorm X)
    (hsign : frobeniusNorm (signMatrix S) ≤ Real.sqrt (r : ℝ)) (k : ℕ) :
    frobeniusNorm (neumannIterate Omega S p k) ≤ ρ' ^ k * Real.sqrt (r : ℝ) := by
  induction k with
  | zero =>
      unfold neumannIterate
      rw [Function.iterate_zero_apply, pow_zero, one_mul]
      exact hsign
  | succ n ih =>
      have hfixed := neumannIterate_tangent_fixed S Omega p n
      have hstep : neumannIterate Omega S p (n + 1)
          = neumannErrorOperator Omega S p (neumannIterate Omega S p n) := by
        unfold neumannIterate; rw [Function.iterate_succ_apply']
      rw [hstep]
      calc frobeniusNorm (neumannErrorOperator Omega S p (neumannIterate Omega S p n))
          ≤ ρ' * frobeniusNorm (neumannIterate Omega S p n) := hcontr _ hfixed
        _ ≤ ρ' * (ρ' ^ n * Real.sqrt (r : ℝ)) :=
            mul_le_mul_of_nonneg_left ih hρ'0
        _ = ρ' ^ (n + 1) * Real.sqrt (r : ℝ) := by rw [pow_succ]; ring

/-! ## STEP 3: per-term spectral bound. -/

theorem neumannCertificateTerm_spectral_bound (S : SVD M r)
    (Omega : Finset (Fin n₁ × Fin n₂)) (p ρ' sbound : ℝ)
    (hp0 : 0 ≤ p)
    (hsamp : ∀ X : RealMatrix n₁ n₂, tangentProjection S X = X →
        frobeniusNorm (samplingProjection Omega X) ≤ sbound * frobeniusNorm X)
    (hsbound0 : 0 ≤ sbound)
    (hiter : ∀ k, frobeniusNorm (neumannIterate Omega S p k) ≤ ρ' ^ k * Real.sqrt (r : ℝ))
    (hρ'0 : 0 ≤ ρ') (k : ℕ) :
    spectralNorm (neumannCertificateTerm Omega S p k)
      ≤ p⁻¹ * (sbound * (ρ' ^ k * Real.sqrt (r : ℝ))) := by
  have hfixed := neumannIterate_tangent_fixed S Omega p k
  -- unfold the cert term and use tangent-fixedness of the iterate
  unfold neumannCertificateTerm
  rw [hfixed]
  set W := samplingProjection Omega (neumannIterate Omega S p k) with hW
  -- spectralNorm (p⁻¹ • normalProjection S W) = |p⁻¹| * spectralNorm (normalProjection S W)
  rw [spectralNorm_smul]
  rw [abs_of_nonneg (inv_nonneg.mpr hp0)]
  -- spectralNorm (normalProjection S W) ≤ frobeniusNorm (normalProjection S W) ≤ frobeniusNorm W
  have h1 : spectralNorm (normalProjection S W) ≤ frobeniusNorm W := by
    calc spectralNorm (normalProjection S W)
        ≤ frobeniusNorm (normalProjection S W) := spectralNorm_le_frobeniusNorm _
      _ ≤ frobeniusNorm W := frobeniusNorm_normalProjection_le S W
  -- frobeniusNorm W = frobeniusNorm (samplingProjection ...) ≤ sbound * frob(iterate k) ≤ sbound*ρ'^k √r
  have h2 : frobeniusNorm W ≤ sbound * (ρ' ^ k * Real.sqrt (r : ℝ)) := by
    calc frobeniusNorm W ≤ sbound * frobeniusNorm (neumannIterate Omega S p k) :=
          hsamp _ hfixed
      _ ≤ sbound * (ρ' ^ k * Real.sqrt (r : ℝ)) :=
          mul_le_mul_of_nonneg_left (hiter k) hsbound0
  have hchain : spectralNorm (normalProjection S W) ≤ sbound * (ρ' ^ k * Real.sqrt (r : ℝ)) :=
    le_trans h1 h2
  exact mul_le_mul_of_nonneg_left hchain (inv_nonneg.mpr hp0)

/-! ## Geometric sum bound. -/

theorem geom_sum_Icc_le {ρ' : ℝ} (hρ'0 : 0 ≤ ρ') (hρ'half : ρ' ≤ 1 / 2) (K : ℕ) :
    (∑ k ∈ Finset.Icc 3 K, ρ' ^ k) ≤ 2 * ρ' ^ 3 := by
  have hIcc : Finset.Icc 3 K = Finset.Ico 3 (K + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  -- ∑ j ∈ range (K+1-3), ρ'^(3+j)
  have hbound : ∀ j ∈ Finset.range (K + 1 - 3), ρ' ^ (3 + j) ≤ ρ' ^ 3 * (1 / 2) ^ j := by
    intro j _
    rw [pow_add]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hρ'0 3)
    exact pow_le_pow_left₀ hρ'0 hρ'half j
  calc (∑ j ∈ Finset.range (K + 1 - 3), ρ' ^ (3 + j))
      ≤ ∑ j ∈ Finset.range (K + 1 - 3), ρ' ^ 3 * (1 / 2) ^ j := Finset.sum_le_sum hbound
    _ = ρ' ^ 3 * ∑ j ∈ Finset.range (K + 1 - 3), (1 / 2 : ℝ) ^ j := by rw [← Finset.mul_sum]
    _ ≤ ρ' ^ 3 * 2 := by
        apply mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (pow_nonneg hρ'0 3)
    _ = 2 * ρ' ^ 3 := by ring

/-! ## STEP 4 + 5: assemble the tail bound for a single partial sum. -/

/-- The partial-sum spectral bound, parametrized by ρ' = max ρ 0. -/
theorem tail_partial_sum_bound (S : SVD M r)
    (Omega : Finset (Fin n₁ × Fin n₂)) (p ρ' sbound : ℝ)
    (hp0 : 0 ≤ p)
    (hsbound0 : 0 ≤ sbound)
    (hρ'0 : 0 ≤ ρ') (hρ'half : ρ' ≤ 1 / 2)
    (hsamp : ∀ X : RealMatrix n₁ n₂, tangentProjection S X = X →
        frobeniusNorm (samplingProjection Omega X) ≤ sbound * frobeniusNorm X)
    (hiter : ∀ k, frobeniusNorm (neumannIterate Omega S p k) ≤ ρ' ^ k * Real.sqrt (r : ℝ))
    (K : ℕ) :
    spectralNorm (∑ k ∈ Finset.Icc 3 K, neumannCertificateTerm Omega S p k)
      ≤ p⁻¹ * sbound * Real.sqrt (r : ℝ) * (2 * ρ' ^ 3) := by
  have hperterm : ∀ k, spectralNorm (neumannCertificateTerm Omega S p k)
      ≤ p⁻¹ * (sbound * (ρ' ^ k * Real.sqrt (r : ℝ))) :=
    fun k => neumannCertificateTerm_spectral_bound S Omega p ρ' sbound hp0 hsamp hsbound0
      hiter hρ'0 k
  calc spectralNorm (∑ k ∈ Finset.Icc 3 K, neumannCertificateTerm Omega S p k)
      ≤ ∑ k ∈ Finset.Icc 3 K, spectralNorm (neumannCertificateTerm Omega S p k) :=
        spectralNorm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 3 K, p⁻¹ * (sbound * (ρ' ^ k * Real.sqrt (r : ℝ))) :=
        Finset.sum_le_sum (fun k _ => hperterm k)
    _ = (p⁻¹ * sbound * Real.sqrt (r : ℝ)) * (∑ k ∈ Finset.Icc 3 K, ρ' ^ k) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ (p⁻¹ * sbound * Real.sqrt (r : ℝ)) * (2 * ρ' ^ 3) := by
        apply mul_le_mul_of_nonneg_left (geom_sum_Icc_le hρ'0 hρ'half K)
        positivity
    _ = p⁻¹ * sbound * Real.sqrt (r : ℝ) * (2 * ρ' ^ 3) := by ring

end MatrixCompletion

open MatrixCompletion

theorem solution (Cdev : ℝ) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ → A0 S μ₀ → A1 S μ₁ →
        tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m ≤ (1 : ℝ) / 2 →
        NeumannErrorOperatorFrobeniusContraction Omega S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m) →
        SampledTangentOperatorFrobeniusBound Omega S
          (Real.sqrt (((3 : ℝ) * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) / 2)) →
        frobeniusNorm (signMatrix S) ≤ Real.sqrt (r : ℝ) →
        NeumannCertificateTailSpectralBound Omega S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 3
          (neumannRemainderFormulaBound Ctail β μ₀ (max n₁ n₂) r m) := by
  refine ⟨2 * Real.sqrt (3 / 2) * |Cdev| ^ 3 + 1, by positivity, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S Omega hn1 hn2 hr hm hμ0 hμ1 hA0 hA1
    hρhalf hcontr hsamp hsign
  -- Notation
  set K0 := max n₁ n₂ with hK0
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set ρ : ℝ := tangentSamplingDeviationScale Cdev β μ₀ K0 r m with hρ
  set ρ' : ℝ := max ρ 0 with hρ'
  set sbound : ℝ := Real.sqrt ((3 * p) / 2) with hsb
  set Ctail : ℝ := 2 * Real.sqrt (3 / 2) * |Cdev| ^ 3 + 1 with hCtail
  -- basic positivity facts
  have hn1R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn1
  have hn2R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn2
  have hnnR : (0 : ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := mul_pos hn1R hn2R
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  have hρ'half : ρ' ≤ 1 / 2 := by
    rw [hρ']; exact max_le hρhalf (by norm_num)
  have hsb0 : 0 ≤ sbound := Real.sqrt_nonneg _
  -- iterate bound
  have hiter : ∀ k, frobeniusNorm (neumannIterate Omega S p k) ≤ ρ' ^ k * Real.sqrt (r : ℝ) := by
    intro k
    apply neumannIterate_frobenius_bound S Omega p ρ' hρ'0 _ hsign k
    intro X hX
    have := hcontr X hX
    -- hcontr : frob (H X) ≤ ρ * frob X ; ρ ≤ ρ' and frob X ≥ 0
    calc frobeniusNorm (neumannErrorOperator Omega S p X)
        ≤ ρ * frobeniusNorm X := this
      _ ≤ ρ' * frobeniusNorm X :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (frobeniusNorm_nonneg X)
  -- sampled bound is exactly hsamp at sbound
  have hsampX : ∀ X : RealMatrix n₁ n₂, tangentProjection S X = X →
      frobeniusNorm (samplingProjection Omega X) ≤ sbound * frobeniusNorm X := hsamp
  -- The remainder formula bound expressed with W
  set W : ℝ := (μ₀ * (K0 : ℝ) * (r : ℝ) * (β * Real.log (K0 : ℝ))) / (m : ℝ) with hW
  -- Unfold the tail predicate
  intro K hK
  -- partial sum bound
  have hpart := tail_partial_sum_bound S Omega p ρ' sbound hp0 hsb0 hρ'0 hρ'half hsampX hiter K
  refine le_trans hpart ?_
  -- Now the arithmetic STEP 5: p⁻¹ * sbound * √r * (2 ρ'^3) ≤ remainderFormulaBound
  -- Case split on m = 0.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0 ⟹ p = 0 ⟹ p⁻¹ = 0 ⟹ LHS = 0 ; RHS ≥ 0.
    have hpz : p = 0 := by rw [hp, hm0]; simp
    rw [hpz]
    simp only [inv_zero, zero_mul]
    -- 0 ≤ remainderFormulaBound
    have hrhs0 : 0 ≤ neumannRemainderFormulaBound Ctail β μ₀ K0 r m := by
      unfold neumannRemainderFormulaBound
      have hC0 : 0 ≤ Ctail := by rw [hCtail]; positivity
      have : 0 ≤ Real.rpow ((μ₀ * (K0:ℝ) * (r:ℝ) * (β * Real.log (K0:ℝ))) / (m:ℝ)) (3/2) :=
        Real.rpow_nonneg (by rw [hm0]; simp) _
      positivity
    exact hrhs0
  · -- m ≥ 1: the genuine arithmetic.
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hppos : 0 < p := by rw [hp]; positivity
    -- K0 ≥ 1, log K0 ≥ 0, W ≥ 0
    have hK01 : (1 : ℝ) ≤ (K0 : ℝ) := by
      rw [hK0]; have : 1 ≤ max n₁ n₂ := le_max_of_le_left hn1
      exact_mod_cast this
    have hK0pos : (0 : ℝ) < (K0 : ℝ) := lt_of_lt_of_le one_pos hK01
    have hlogK0 : 0 ≤ Real.log (K0 : ℝ) := Real.log_nonneg hK01
    have hWpos : 0 ≤ W := by
      rw [hW]
      have hnum : 0 ≤ μ₀ * (K0:ℝ) * (r:ℝ) * (β * Real.log (K0:ℝ)) := by
        have hβ0 : 0 ≤ β := le_of_lt (lt_trans (by norm_num) hβ)
        have hμ00 : 0 ≤ μ₀ := le_trans zero_le_one hμ0
        positivity
      exact div_nonneg hnum (le_of_lt hmR)
    -- ρ ≤ |Cdev| * √W and ρ' ≤ |Cdev| * √W
    have hρeq : ρ = Cdev * Real.sqrt W := by rw [hρ]; rfl
    have hρ'_le : ρ' ≤ |Cdev| * Real.sqrt W := by
      rw [hρ']
      apply max_le
      · rw [hρeq]
        exact mul_le_mul_of_nonneg_right (le_abs_self Cdev) (Real.sqrt_nonneg _)
      · positivity
    -- (√W)^3 = W^(3/2)
    have hsqrtW3 : (Real.sqrt W) ^ 3 = Real.rpow W (3 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (W ^ ((1:ℝ) / 2)) 3, ← Real.rpow_mul hWpos]
      norm_num
    -- ρ'^3 ≤ (|Cdev| * √W)^3 = |Cdev|^3 * W^(3/2)
    have hρ'cube : ρ' ^ 3 ≤ |Cdev| ^ 3 * Real.rpow W (3 / 2) := by
      calc ρ' ^ 3 ≤ (|Cdev| * Real.sqrt W) ^ 3 := pow_le_pow_left₀ hρ'0 hρ'_le 3
        _ = |Cdev| ^ 3 * (Real.sqrt W) ^ 3 := by ring
        _ = |Cdev| ^ 3 * Real.rpow W (3 / 2) := by rw [hsqrtW3]
    -- prefactor identity: p⁻¹ * sbound * √r = √(3/2) * √((n₁n₂) r / m)
    have hpre : p⁻¹ * sbound * Real.sqrt (r : ℝ)
        = Real.sqrt (3 / 2) * Real.sqrt (((n₁:ℝ) * (n₂:ℝ)) * (r:ℝ) / (m:ℝ)) := by
      rw [hsb]
      -- sbound = √(3p/2);  p⁻¹ = √(p⁻²)
      have hinv : p⁻¹ = Real.sqrt (p⁻¹ ^ 2) := by
        rw [Real.sqrt_sq (le_of_lt (inv_pos.mpr hppos))]
      rw [hinv]
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
        ← Real.sqrt_mul (by positivity)]
      congr 1
      -- p⁻¹^2 * (3p/2) * r = (3/2) * (n₁n₂ r / m)
      rw [hp]
      field_simp
    -- n₁n₂ ≤ K0²  ⟹  √(n₁n₂ r/m) ≤ √(K0² r/m)
    have hnnK0 : ((n₁:ℝ) * (n₂:ℝ)) ≤ (K0:ℝ) ^ 2 := by
      have h1 : (n₁:ℝ) ≤ (K0:ℝ) := by rw [hK0]; exact_mod_cast le_max_left n₁ n₂
      have h2 : (n₂:ℝ) ≤ (K0:ℝ) := by rw [hK0]; exact_mod_cast le_max_right n₁ n₂
      nlinarith [hn1R.le, hn2R.le, hK0pos.le]
    have hsqrtmono : Real.sqrt (((n₁:ℝ) * (n₂:ℝ)) * (r:ℝ) / (m:ℝ))
        ≤ Real.sqrt ((K0:ℝ)^2 * (r:ℝ) / (m:ℝ)) := by
      apply Real.sqrt_le_sqrt
      gcongr
    -- assemble
    unfold neumannRemainderFormulaBound
    rw [← hW]
    -- LHS = (p⁻¹ sbound √r) * (2 ρ'^3) ; reorganize
    have hpre0 : 0 ≤ p⁻¹ * sbound * Real.sqrt (r : ℝ) := by
      rw [hpre]; positivity
    have hrpow0 : 0 ≤ Real.rpow W (3 / 2) := Real.rpow_nonneg hWpos _
    calc p⁻¹ * sbound * Real.sqrt (r : ℝ) * (2 * ρ' ^ 3)
        ≤ p⁻¹ * sbound * Real.sqrt (r : ℝ) * (2 * (|Cdev| ^ 3 * Real.rpow W (3 / 2))) := by
          apply mul_le_mul_of_nonneg_left _ hpre0
          exact mul_le_mul_of_nonneg_left hρ'cube (by norm_num)
      _ = (p⁻¹ * sbound * Real.sqrt (r : ℝ)) * (2 * |Cdev| ^ 3) * Real.rpow W (3 / 2) := by ring
      _ = (Real.sqrt (3 / 2) * Real.sqrt (((n₁:ℝ) * (n₂:ℝ)) * (r:ℝ) / (m:ℝ)))
            * (2 * |Cdev| ^ 3) * Real.rpow W (3 / 2) := by rw [hpre]
      _ ≤ (Real.sqrt (3 / 2) * Real.sqrt ((K0:ℝ)^2 * (r:ℝ) / (m:ℝ)))
            * (2 * |Cdev| ^ 3) * Real.rpow W (3 / 2) := by
          apply mul_le_mul_of_nonneg_right _ hrpow0
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hsqrtmono (Real.sqrt_nonneg _)
      _ = (2 * Real.sqrt (3 / 2) * |Cdev| ^ 3)
            * Real.sqrt ((K0:ℝ)^2 * (r:ℝ) / (m:ℝ)) * Real.rpow W (3 / 2) := by ring
      _ ≤ Ctail * Real.sqrt ((K0:ℝ)^2 * (r:ℝ) / (m:ℝ)) * Real.rpow W (3 / 2) := by
          apply mul_le_mul_of_nonneg_right _ hrpow0
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          rw [hCtail]; linarith
