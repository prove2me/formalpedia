-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_geom_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T13:18:14.777485+00:00
-- url     : https://prove2.me/submissions/a7e529e8-d62a-4858-8d62-92cb6997f056

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
import Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
import Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_bound_min_dim
import Theorems.Thm_sign_matrix_spectral_norm_le_one

open MatrixCompletion

/-! Helper lemmas for the honest rectangular Lemma 6.8 entry bound. -/

/-- `matrixInner` against a coordinate matrix picks out the entry. -/
theorem h1_matrixInner_coordinateMatrix {n₁ n₂ : ℕ}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The coordinate kernel is the entry of the projected coordinate matrix. -/
theorem h1_kernel_eq_proj_entry {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a i : Fin n₁) (b j : Fin n₂) :
    tangentCoordinateKernel S a b i j =
      tangentProjection S (coordinateMatrix a b) i j := by
  unfold tangentCoordinateKernel
  exact h1_matrixInner_coordinateMatrix _ i j

/-- Linearity of the tangent projection over the coordinate expansion:
`Σ_w D_w ⟪P_T(e_w), e_ij⟫ = (P_T D)_ij`. -/
theorem h1_sum_kernel_eq_proj {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (D : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    (∑ w : Fin n₁ × Fin n₂, D w.1 w.2 * tangentCoordinateKernel S w.1 w.2 i j) =
      tangentProjection S D i j := by
  have hker : ∀ w : Fin n₁ × Fin n₂,
      tangentCoordinateKernel S w.1 w.2 i j =
        tangentProjection S (coordinateMatrix w.1 w.2) i j :=
    fun w => h1_kernel_eq_proj_entry S w.1 i w.2 j
  simp only [hker]
  unfold tangentProjection leftSingularProjection rightSingularProjection
    twoSidedSingularProjection
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [Fintype.sum_prod_type]
  simp only [coordinateMatrix]
  have hL : ∀ (a : Fin n₁) (b : Fin n₂),
      (∑ c : Fin n₁, (∑ k, S.u k i * S.u k c) *
        (if c = a ∧ j = b then (1:ℝ) else 0)) =
        (if j = b then (∑ k, S.u k i * S.u k a) else 0) := by
    intro a b
    rw [Finset.sum_eq_single a]
    · by_cases h : j = b <;> simp [h]
    · intro c _ hc; simp [hc]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hR : ∀ (a : Fin n₁) (b : Fin n₂),
      (∑ d : Fin n₂, (if i = a ∧ d = b then (1:ℝ) else 0) *
        (∑ l, S.v l d * S.v l j)) =
        (if i = a then (∑ l, S.v l b * S.v l j) else 0) := by
    intro a b
    rw [Finset.sum_eq_single b]
    · by_cases h : i = a <;> simp [h]
    · intro d _ hd; simp [hd]
    · intro h; exact absurd (Finset.mem_univ b) h
  have hT : ∀ (a : Fin n₁) (b : Fin n₂),
      (∑ c : Fin n₁, ∑ d : Fin n₂, (∑ k, S.u k i * S.u k c) *
          (if c = a ∧ d = b then (1:ℝ) else 0) *
            (∑ l, S.v l d * S.v l j)) =
        (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) := by
    intro a b
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro d _ hd; simp [hd]
      · intro h; exact absurd (Finset.mem_univ b) h
    · intro c _ hc
      apply Finset.sum_eq_zero
      intro d _
      simp [hc]
    · intro h; exact absurd (Finset.mem_univ a) h
  calc
    ∑ a, ∑ b, D a b *
        ((∑ c, (∑ k, S.u k i * S.u k c) * if c = a ∧ j = b then (1:ℝ) else 0) +
          (∑ d, (if i = a ∧ d = b then (1:ℝ) else 0) * ∑ l, S.v l d * S.v l j) -
          ∑ c, ∑ d, ((∑ k, S.u k i * S.u k c) *
            if c = a ∧ d = b then (1:ℝ) else 0) * ∑ l, S.v l d * S.v l j)
      = ∑ a, ∑ b,
          (D a b * (if j = b then ∑ k, S.u k i * S.u k a else 0) +
            D a b * (if i = a then ∑ l, S.v l b * S.v l j else 0) -
            D a b * ((∑ k, S.u k i * S.u k a) * ∑ l, S.v l b * S.v l j)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hL a b, hR a b, hT a b]
        ring
    _ = (∑ a, ∑ b, D a b * (if j = b then ∑ k, S.u k i * S.u k a else 0)) +
          (∑ a, ∑ b, D a b * (if i = a then ∑ l, S.v l b * S.v l j else 0)) -
          ∑ a, ∑ b, D a b * ((∑ k, S.u k i * S.u k a) * ∑ l, S.v l b * S.v l j) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = ∑ a, (∑ k, S.u k i * S.u k a) * D a j +
          ∑ b, D i b * ∑ k, S.v k b * S.v k j -
          ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * D a b * ∑ l, S.v l b * S.v l j := by
        congr 1
        · congr 1
          · refine Finset.sum_congr rfl fun a _ => ?_
            have hcollapse : (∑ b, D a b * (if j = b then ∑ k, S.u k i * S.u k a else 0)) =
                ∑ b, (if j = b then D a b * ∑ k, S.u k i * S.u k a else 0) := by
              refine Finset.sum_congr rfl fun b _ => ?_
              by_cases h : j = b <;> simp [h]
            rw [hcollapse, Finset.sum_ite_eq]
            simp [mul_comm]
          · have hcollapse : ∀ a : Fin n₁,
                (∑ b, D a b * (if i = a then ∑ l, S.v l b * S.v l j else 0)) =
                  (if i = a then ∑ b, D a b * ∑ l, S.v l b * S.v l j else 0) := by
              intro a
              by_cases h : i = a <;> simp [h]
            rw [Finset.sum_congr rfl fun a _ => hcollapse a, Finset.sum_ite_eq]
            simp
        · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          ring

/-- Row idempotence energy: `Σ_a (Σ_k u_ki u_ka)² = Σ_k u_ki²`. -/
theorem h1_proj_row_energy {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) :
    (∑ a : Fin n₁, (∑ k, S.u k i * S.u k a) ^ 2) = ∑ k, (S.u k i) ^ 2 := by
  have hexp : ∀ a : Fin n₁, (∑ k, S.u k i * S.u k a) ^ 2 =
      ∑ k, ∑ l, (S.u k i * S.u l i) * (S.u k a * S.u l a) := by
    intro a
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [Finset.sum_congr rfl fun a _ => hexp a]
  rw [Finset.sum_comm]
  have hswap : ∀ k : Fin r,
      (∑ a : Fin n₁, ∑ l, (S.u k i * S.u l i) * (S.u k a * S.u l a)) =
        ∑ l, (S.u k i * S.u l i) * ∑ a, S.u k a * S.u l a := by
    intro k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ => hswap k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [S.u_orthonormal k k]
    simp [sq]
  · intro l _ hl
    rw [S.u_orthonormal k l, if_neg (fun h => hl h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Column idempotence energy: `Σ_b (Σ_l v_lb v_lj)² = Σ_l v_lj²`. -/
theorem h1_proj_col_energy {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (j : Fin n₂) :
    (∑ b : Fin n₂, (∑ l, S.v l b * S.v l j) ^ 2) = ∑ l, (S.v l j) ^ 2 := by
  have hexp : ∀ b : Fin n₂, (∑ l, S.v l b * S.v l j) ^ 2 =
      ∑ k, ∑ l, (S.v k j * S.v l j) * (S.v k b * S.v l b) := by
    intro b
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [Finset.sum_congr rfl fun b _ => hexp b]
  rw [Finset.sum_comm]
  have hswap : ∀ k : Fin r,
      (∑ b : Fin n₂, ∑ l, (S.v k j * S.v l j) * (S.v k b * S.v l b)) =
        ∑ l, (S.v k j * S.v l j) * ∑ b, S.v k b * S.v l b := by
    intro k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ => hswap k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [S.v_orthonormal k k]
    simp [sq]
  · intro l _ hl
    rw [S.v_orthonormal k l, if_neg (fun h => hl h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Entry formula for the sign matrix. -/
theorem h1_signMatrix_apply {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : Fin n₁) (b : Fin n₂) :
    signMatrix S a b = ∑ k, S.u k a * S.v k b := by
  unfold signMatrix
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply]

/-- Column energy of the sign matrix collapses by `u`-orthonormality. -/
theorem h1_sign_col_energy {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (j : Fin n₂) :
    (∑ a : Fin n₁, (signMatrix S a j) ^ 2) = ∑ k, (S.v k j) ^ 2 := by
  have hexp : ∀ a : Fin n₁, (signMatrix S a j) ^ 2 =
      ∑ k, ∑ l, (S.v k j * S.v l j) * (S.u k a * S.u l a) := by
    intro a
    rw [h1_signMatrix_apply S a j, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [Finset.sum_congr rfl fun a _ => hexp a]
  rw [Finset.sum_comm]
  have hswap : ∀ k : Fin r,
      (∑ a : Fin n₁, ∑ l, (S.v k j * S.v l j) * (S.u k a * S.u l a)) =
        ∑ l, (S.v k j * S.v l j) * ∑ a, S.u k a * S.u l a := by
    intro k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ => hswap k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [S.u_orthonormal k k]
    simp [sq]
  · intro l _ hl
    rw [S.u_orthonormal k l, if_neg (fun h => hl h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Row energy of the sign matrix collapses by `v`-orthonormality. -/
theorem h1_sign_row_energy {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) :
    (∑ b : Fin n₂, (signMatrix S i b) ^ 2) = ∑ k, (S.u k i) ^ 2 := by
  have hexp : ∀ b : Fin n₂, (signMatrix S i b) ^ 2 =
      ∑ k, ∑ l, (S.u k i * S.u l i) * (S.v k b * S.v l b) := by
    intro b
    rw [h1_signMatrix_apply S i b, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [Finset.sum_congr rfl fun b _ => hexp b]
  rw [Finset.sum_comm]
  have hswap : ∀ k : Fin r,
      (∑ b : Fin n₂, ∑ l, (S.u k i * S.u l i) * (S.v k b * S.v l b)) =
        ∑ l, (S.u k i * S.u l i) * ∑ b, S.v k b * S.v l b := by
    intro k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ => hswap k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [S.v_orthonormal k k]
    simp [sq]
  · intro l _ hl
    rw [S.v_orthonormal k l, if_neg (fun h => hl h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Removing one index from a full sum: `Σ_w (if w = z then 0 else f w) = Σ f - f z`. -/
theorem h1_sum_ite_ne_eq_sub {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (z : α) :
    (∑ w : α, if w = z then 0 else f w) = (∑ w : α, f w) - f z := by
  have h : ∀ w : α, (if w = z then (0:ℝ) else f w) =
      f w - (if w = z then f z else 0) := by
    intro w
    by_cases hw : w = z <;> simp [hw]
  rw [Finset.sum_congr rfl fun w _ => h w, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ z (fun _ => f z)]
  simp

/-- Bilinear form against a matrix is controlled by the spectral norm and the
Euclidean norms of the two vectors. -/
theorem h1_bilinear_le_spectralNorm {n₁ n₂ : ℕ} (A : Matrix (Fin n₁) (Fin n₂) ℝ)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) :
    |∑ a, ∑ b, x a * A a b * y b| ≤
      spectralNorm A * Real.sqrt (∑ a, x a ^ 2) * Real.sqrt (∑ b, y b ^ 2) := by
  have hx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n₁))‖ = Real.sqrt (∑ a, x a ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have hy : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n₂))‖ = Real.sqrt (∑ b, y b ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have happly : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))
      (WithLp.toLp 2 y) = WithLp.toLp 2 (A.mulVec y) := rfl
  have hinner : inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n₁))
      (WithLp.toLp 2 (A.mulVec y)) = ∑ a, ∑ b, x a * A a b * y b := by
    have hdot : inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n₁))
        (WithLp.toLp 2 (A.mulVec y)) = dotProduct (A.mulVec y) (star x) := rfl
    rw [hdot, star_trivial, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have h1 : |inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n₁))
      ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) (WithLp.toLp 2 y))| ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n₁))‖ *
        ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) (WithLp.toLp 2 y)‖ :=
    abs_real_inner_le_norm _ _
  have h2 : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) (WithLp.toLp 2 y)‖ ≤
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ *
        ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n₂))‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [happly, hinner] at h1
  unfold spectralNorm
  calc |∑ a, ∑ b, x a * A a b * y b|
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n₁))‖ *
        ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) (WithLp.toLp 2 y)‖ :=
        h1
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n₁))‖ *
        (‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ *
          ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n₂))‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ *
        Real.sqrt (∑ a, x a ^ 2) * Real.sqrt (∑ b, y b ^ 2) := by
        rw [hx, hy]; ring

/-- Cauchy–Schwarz in absolute-value/sqrt form. -/
theorem h1_abs_sum_mul_le {N : ℕ} (x y : Fin N → ℝ) :
    |∑ a, x a * y a| ≤ Real.sqrt (∑ a, x a ^ 2) * Real.sqrt (∑ a, y a ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  refine (Real.sqrt_le_sqrt h).trans_eq ?_
  rw [Real.sqrt_mul (Finset.sum_nonneg fun a _ => sq_nonneg _)]

/-- H1: honest rectangular Lemma 6.8 entry bound for the first-index-distinct
mean coefficient matrix, from A0 alone. -/
theorem solution :
    ∃ C68 : ℝ, 0 < C68 ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r) (p : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < p → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) ≤
          C68 * p⁻¹ * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
            (μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 + μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Cker, hCker, hkerB⟩ := tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
  obtain ⟨Cdiag, hCdiag, hdiagB⟩ := tangent_diagonal_multiplier_spectral_norm_bound_min_dim
  refine ⟨2 * Cker + Cdiag + Cker ^ 2, by positivity, ?_⟩
  intro n₁ n₂ r M μ₀ S p hn₁ hn₂ hr hp hμ₀ hA0
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hμ₀0 : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hmn : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hmnR : (0 : ℝ) < (↑(min n₁ n₂) : ℝ) := by exact_mod_cast hmn
  have hpinv0 : (0 : ℝ) < p⁻¹ := inv_pos.mpr hp
  -- opaque scales
  obtain ⟨t, ht_def⟩ : ∃ x : ℝ, x = μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := ⟨_, rfl⟩
  obtain ⟨g, hg_def⟩ : ∃ x : ℝ, x = μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) :=
    ⟨_, rfl⟩
  have hsqrtn : (0 : ℝ) < Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos hn₁R hn₂R)
  have ht0 : (0 : ℝ) < t := by rw [ht_def]; positivity
  have hg0 : (0 : ℝ) < g := by
    rw [hg_def]; exact div_pos (mul_pos hμ₀0 hrR) hsqrtn
  obtain ⟨CK, hCK_def⟩ : ∃ x : ℝ, x = Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) :=
    ⟨_, rfl⟩
  have hCK0 : (0 : ℝ) < CK := by
    rw [hCK_def]
    exact mul_pos (mul_pos hCker hμ₀0) (div_pos hrR hmnR)
  have hCKt : CK = Cker * t := by rw [hCK_def, ht_def]; ring
  -- singular coordinate energies from A0 (as in G1)
  have energy_le :
      ∀ (N : ℕ) (w : Fin r → Fin N → ℝ),
        0 < N →
        (N : ℝ) / (r : ℝ) * (⨆ i : Fin N, ∑ k, (w k i) ^ 2) ≤ μ₀ →
        ∀ _ : Nonempty (Fin N),
        ∀ i : Fin N, ∑ k, (w k i) ^ 2 ≤ μ₀ * (r : ℝ) / (N : ℝ) := by
    intro N w hN hcoh hNe i
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hbdd : BddAbove (Set.range fun i : Fin N => ∑ k, (w k i) ^ 2) :=
      Set.Finite.bddAbove (Set.finite_range _)
    have hle : (∑ k, (w k i) ^ 2) ≤ ⨆ i : Fin N, ∑ k, (w k i) ^ 2 :=
      le_ciSup hbdd i
    have hpos : (0 : ℝ) < (N : ℝ) / (r : ℝ) := div_pos hNR hrR
    have hcoh' : (⨆ i : Fin N, ∑ k, (w k i) ^ 2) * ((N : ℝ) / (r : ℝ)) ≤ μ₀ := by
      calc (⨆ i : Fin N, ∑ k, (w k i) ^ 2) * ((N : ℝ) / (r : ℝ))
          = (N : ℝ) / (r : ℝ) * ⨆ i : Fin N, ∑ k, (w k i) ^ 2 := by ring
        _ ≤ μ₀ := hcoh
    have h2 := (le_div_iff₀ hpos).mpr hcoh'
    refine hle.trans (h2.trans_eq ?_)
    field_simp
  have hU := energy_le n₁ S.u hn₁ hA0.1 ‹Nonempty (Fin n₁)›
  have hV := energy_le n₂ S.v hn₂ hA0.2 ‹Nonempty (Fin n₂)›
  -- entry bound for the sign matrix
  have hEsup := entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
    n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have habs_le_sup : ∀ (X : Matrix (Fin n₁) (Fin n₂) ℝ) (a : Fin n₁) (b : Fin n₂),
      |X a b| ≤ entrySupNorm X := by
    intro X a b
    have h1 : |X a b| ≤ ⨆ j : Fin n₂, |X a j| :=
      le_ciSup (f := fun j : Fin n₂ => |X a j|)
        (Set.Finite.bddAbove (Set.finite_range _)) b
    have h2 : (⨆ j : Fin n₂, |X a j|) ≤ ⨆ i : Fin n₁, ⨆ j : Fin n₂, |X i j| :=
      le_ciSup (f := fun i : Fin n₁ => ⨆ j : Fin n₂, |X i j|)
        (Set.Finite.bddAbove (Set.finite_range _)) a
    exact h1.trans h2
  have hE_entry : ∀ (a : Fin n₁) (b : Fin n₂), |signMatrix S a b| ≤ g := by
    intro a b
    refine (habs_le_sup _ a b).trans ?_
    rw [hg_def]
    exact hEsup
  -- diagonal kernel bound
  have hK_entry : ∀ (a : Fin n₁) (b : Fin n₂),
      |tangentCoordinateKernel S a b a b| ≤ CK := by
    intro a b
    rw [hCK_def]
    exact hkerB n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 a b
  -- the diagonal-multiplier matrix D
  set D : Matrix (Fin n₁) (Fin n₂) ℝ := tangentDiagonalMultiplier S (signMatrix S)
    with hD_def
  have hD_apply : ∀ (a : Fin n₁) (b : Fin n₂),
      D a b = signMatrix S a b * tangentCoordinateKernel S a b a b := fun a b => rfl
  have hD_entry : ∀ (a : Fin n₁) (b : Fin n₂), |D a b| ≤ g * CK := by
    intro a b
    rw [hD_apply a b, abs_mul]
    exact mul_le_mul (hE_entry a b) (hK_entry a b) (abs_nonneg _) (le_of_lt hg0)
  have hspecD : spectralNorm D ≤ Cdiag * t := by
    have h1 := hdiagB n₁ n₂ r M μ₀ S (signMatrix S) hn₁ hn₂ hr hμ₀ hA0
    have h2 := sign_matrix_spectral_norm_le_one S
    have h3 : (0 : ℝ) ≤ Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by positivity
    calc spectralNorm D
        ≤ Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * spectralNorm (signMatrix S) := h1
      _ ≤ Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * 1 :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = Cdiag * t := by rw [ht_def]; ring
  -- squared-column/row energies of D
  have hK_sq : ∀ (a : Fin n₁) (b : Fin n₂),
      (tangentCoordinateKernel S a b a b) ^ 2 ≤ CK ^ 2 := by
    intro a b
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hK_entry a b) 2
  have hDcol : ∀ j : Fin n₂,
      (∑ a, (D a j) ^ 2) ≤ CK ^ 2 * (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
    intro j
    have h1 : ∀ a : Fin n₁, (D a j) ^ 2 ≤ CK ^ 2 * (signMatrix S a j) ^ 2 := by
      intro a
      calc (D a j) ^ 2
          = (signMatrix S a j) ^ 2 * (tangentCoordinateKernel S a j a j) ^ 2 := by
            rw [hD_apply a j]; ring
        _ ≤ (signMatrix S a j) ^ 2 * CK ^ 2 :=
            mul_le_mul_of_nonneg_left (hK_sq a j) (sq_nonneg _)
        _ = CK ^ 2 * (signMatrix S a j) ^ 2 := by ring
    calc (∑ a, (D a j) ^ 2)
        ≤ ∑ a, CK ^ 2 * (signMatrix S a j) ^ 2 :=
          Finset.sum_le_sum fun a _ => h1 a
      _ = CK ^ 2 * ∑ a, (signMatrix S a j) ^ 2 := by rw [Finset.mul_sum]
      _ = CK ^ 2 * ∑ k, (S.v k j) ^ 2 := by rw [h1_sign_col_energy]
      _ ≤ CK ^ 2 * (μ₀ * (r : ℝ) / (n₂ : ℝ)) :=
          mul_le_mul_of_nonneg_left (hV j) (sq_nonneg _)
  have hDrow : ∀ i : Fin n₁,
      (∑ b, (D i b) ^ 2) ≤ CK ^ 2 * (μ₀ * (r : ℝ) / (n₁ : ℝ)) := by
    intro i
    have h1 : ∀ b : Fin n₂, (D i b) ^ 2 ≤ CK ^ 2 * (signMatrix S i b) ^ 2 := by
      intro b
      calc (D i b) ^ 2
          = (signMatrix S i b) ^ 2 * (tangentCoordinateKernel S i b i b) ^ 2 := by
            rw [hD_apply i b]; ring
        _ ≤ (signMatrix S i b) ^ 2 * CK ^ 2 :=
            mul_le_mul_of_nonneg_left (hK_sq i b) (sq_nonneg _)
        _ = CK ^ 2 * (signMatrix S i b) ^ 2 := by ring
    calc (∑ b, (D i b) ^ 2)
        ≤ ∑ b, CK ^ 2 * (signMatrix S i b) ^ 2 :=
          Finset.sum_le_sum fun b _ => h1 b
      _ = CK ^ 2 * ∑ b, (signMatrix S i b) ^ 2 := by rw [Finset.mul_sum]
      _ = CK ^ 2 * ∑ k, (S.u k i) ^ 2 := by rw [h1_sign_row_energy]
      _ ≤ CK ^ 2 * (μ₀ * (r : ℝ) / (n₁ : ℝ)) :=
          mul_le_mul_of_nonneg_left (hU i) (sq_nonneg _)
  -- the sqrt product identity
  have hsqrt_prod : Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
      Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) = g := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show μ₀ * (r : ℝ) / (n₁ : ℝ) * (μ₀ * (r : ℝ) / (n₂ : ℝ)) =
        (μ₀ * (r : ℝ)) ^ 2 / ((n₁ : ℝ) * (n₂ : ℝ)) by
      field_simp
      try ring]
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity), hg_def]
  -- bounds for the three projection pieces
  have hleft : ∀ (i : Fin n₁) (j : Fin n₂),
      |leftSingularProjection S D i j| ≤ CK * g := by
    intro i j
    have hL0 : leftSingularProjection S D i j =
        ∑ a, (∑ k, S.u k i * S.u k a) * D a j := rfl
    rw [hL0]
    refine (h1_abs_sum_mul_le (fun a => ∑ k, S.u k i * S.u k a) (fun a => D a j)).trans ?_
    have h1 : Real.sqrt (∑ a, (∑ k, S.u k i * S.u k a) ^ 2) ≤
        Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) := by
      apply Real.sqrt_le_sqrt
      rw [h1_proj_row_energy S i]
      exact hU i
    have h2 : Real.sqrt (∑ a, (D a j) ^ 2) ≤ CK * Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
      refine (Real.sqrt_le_sqrt (hDcol j)).trans_eq ?_
      rw [Real.sqrt_mul (sq_nonneg CK), Real.sqrt_sq (le_of_lt hCK0)]
    calc Real.sqrt (∑ a, (∑ k, S.u k i * S.u k a) ^ 2) * Real.sqrt (∑ a, (D a j) ^ 2)
        ≤ Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          (CK * Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ))) :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = CK * (Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ))) := by ring
      _ = CK * g := by rw [hsqrt_prod]
  have hright : ∀ (i : Fin n₁) (j : Fin n₂),
      |rightSingularProjection S D i j| ≤ CK * g := by
    intro i j
    have hR0 : rightSingularProjection S D i j =
        ∑ b, D i b * (∑ k, S.v k b * S.v k j) := rfl
    rw [hR0]
    refine (h1_abs_sum_mul_le (fun b => D i b) (fun b => ∑ k, S.v k b * S.v k j)).trans ?_
    have h1 : Real.sqrt (∑ b, (D i b) ^ 2) ≤ CK * Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) := by
      refine (Real.sqrt_le_sqrt (hDrow i)).trans_eq ?_
      rw [Real.sqrt_mul (sq_nonneg CK), Real.sqrt_sq (le_of_lt hCK0)]
    have h2 : Real.sqrt (∑ b, (∑ k, S.v k b * S.v k j) ^ 2) ≤
        Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
      apply Real.sqrt_le_sqrt
      rw [h1_proj_col_energy S j]
      exact hV j
    calc Real.sqrt (∑ b, (D i b) ^ 2) * Real.sqrt (∑ b, (∑ k, S.v k b * S.v k j) ^ 2)
        ≤ CK * Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _)
            (mul_nonneg (le_of_lt hCK0) (Real.sqrt_nonneg _))
      _ = CK * (Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ))) := by ring
      _ = CK * g := by rw [hsqrt_prod]
  have htwo : ∀ (i : Fin n₁) (j : Fin n₂),
      |twoSidedSingularProjection S D i j| ≤ Cdiag * t * g := by
    intro i j
    have hT0 : twoSidedSingularProjection S D i j =
        ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * D a b * (∑ l, S.v l b * S.v l j) := rfl
    rw [hT0]
    refine (h1_bilinear_le_spectralNorm D (fun a => ∑ k, S.u k i * S.u k a)
      (fun b => ∑ l, S.v l b * S.v l j)).trans ?_
    have h1 : Real.sqrt (∑ a, (∑ k, S.u k i * S.u k a) ^ 2) ≤
        Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) := by
      apply Real.sqrt_le_sqrt
      rw [h1_proj_row_energy S i]
      exact hU i
    have h2 : Real.sqrt (∑ b, (∑ l, S.v l b * S.v l j) ^ 2) ≤
        Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
      apply Real.sqrt_le_sqrt
      rw [h1_proj_col_energy S j]
      exact hV j
    have hs1 : (0 : ℝ) ≤ Real.sqrt (∑ a, (∑ k, S.u k i * S.u k a) ^ 2) :=
      Real.sqrt_nonneg _
    have hs2 : (0 : ℝ) ≤ Real.sqrt (∑ b, (∑ l, S.v l b * S.v l j) ^ 2) :=
      Real.sqrt_nonneg _
    have hspecD0 : (0 : ℝ) ≤ spectralNorm D := by
      unfold spectralNorm; exact norm_nonneg _
    have hCt0 : (0 : ℝ) ≤ Cdiag * t := mul_nonneg (le_of_lt hCdiag) (le_of_lt ht0)
    calc spectralNorm D * Real.sqrt (∑ a, (∑ k, S.u k i * S.u k a) ^ 2) *
          Real.sqrt (∑ b, (∑ l, S.v l b * S.v l j) ^ 2)
        ≤ (Cdiag * t) * Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
          refine mul_le_mul ?_ h2 hs2 ?_
          · exact mul_le_mul hspecD h1 hs1 hCt0
          · exact mul_nonneg hCt0 (Real.sqrt_nonneg _)
      _ = Cdiag * t * (Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ))) := by ring
      _ = Cdiag * t * g := by rw [hsqrt_prod]
  -- per-entry bound for the coefficient matrix
  have hFentry : ∀ (i : Fin n₁) (j : Fin n₂),
      |quadraticFirstIndexDistinctMeanCoefficientMatrix S p i j| ≤
        (2 * Cker + Cdiag + Cker ^ 2) * p⁻¹ * t * g * (1 + t) := by
    intro i j
    -- the structural identity F_ij = p⁻¹ ((P_T D)_ij - D_ij K_ij,ij)
    have hid : quadraticFirstIndexDistinctMeanCoefficientMatrix S p i j =
        p⁻¹ * (tangentProjection S D i j -
          D i j * tangentCoordinateKernel S i j i j) := by
      show p⁻¹ * (∑ w2 : Fin n₁ × Fin n₂, if w2 = (i, j) then 0 else
          signMatrix S w2.1 w2.2 * tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
            tangentCoordinateKernel S w2.1 w2.2 i j) = _
      congr 1
      rw [h1_sum_ite_ne_eq_sub (fun w : Fin n₁ × Fin n₂ =>
        signMatrix S w.1 w.2 * tangentCoordinateKernel S w.1 w.2 w.1 w.2 *
          tangentCoordinateKernel S w.1 w.2 i j) (i, j)]
      congr 1
      exact h1_sum_kernel_eq_proj S D i j
    rw [hid, abs_mul, abs_of_pos hpinv0]
    -- triangle inequality across the four pieces
    have hproj_split : tangentProjection S D i j =
        leftSingularProjection S D i j + rightSingularProjection S D i j -
          twoSidedSingularProjection S D i j := rfl
    have hdiagterm : |D i j * tangentCoordinateKernel S i j i j| ≤ g * CK * CK := by
      rw [abs_mul]
      exact mul_le_mul (hD_entry i j) (hK_entry i j) (abs_nonneg _)
        (mul_nonneg (le_of_lt hg0) (le_of_lt hCK0))
    have habs : |tangentProjection S D i j -
        D i j * tangentCoordinateKernel S i j i j| ≤
        CK * g + CK * g + Cdiag * t * g + g * CK * CK := by
      rw [hproj_split]
      calc |leftSingularProjection S D i j + rightSingularProjection S D i j -
            twoSidedSingularProjection S D i j -
            D i j * tangentCoordinateKernel S i j i j|
          ≤ |leftSingularProjection S D i j + rightSingularProjection S D i j -
              twoSidedSingularProjection S D i j| +
            |D i j * tangentCoordinateKernel S i j i j| := abs_sub _ _
        _ ≤ (|leftSingularProjection S D i j + rightSingularProjection S D i j| +
              |twoSidedSingularProjection S D i j|) +
            |D i j * tangentCoordinateKernel S i j i j| := by
            have h := abs_sub (leftSingularProjection S D i j +
              rightSingularProjection S D i j) (twoSidedSingularProjection S D i j)
            exact add_le_add h le_rfl
        _ ≤ ((|leftSingularProjection S D i j| + |rightSingularProjection S D i j|) +
              |twoSidedSingularProjection S D i j|) +
            |D i j * tangentCoordinateKernel S i j i j| := by
            have h := abs_add_le (leftSingularProjection S D i j)
              (rightSingularProjection S D i j)
            exact add_le_add (add_le_add h le_rfl) le_rfl
        _ ≤ ((CK * g + CK * g) + Cdiag * t * g) + g * CK * CK := by
            have h1 := add_le_add (add_le_add (hleft i j) (hright i j)) (htwo i j)
            exact add_le_add h1 hdiagterm
        _ = CK * g + CK * g + Cdiag * t * g + g * CK * CK := by ring
    -- scalar arithmetic to fold into (1 + t)
    have harith : CK * g + CK * g + Cdiag * t * g + g * CK * CK ≤
        (2 * Cker + Cdiag + Cker ^ 2) * t * g * (1 + t) := by
      have hstep : CK * g + CK * g + Cdiag * t * g + g * CK * CK =
          2 * (Cker * t) * g + Cdiag * t * g + g * (Cker * t) * (Cker * t) := by
        rw [hCKt]; ring
      have hextra : (0 : ℝ) ≤ Cker ^ 2 * t * g + (2 * Cker + Cdiag) * t ^ 2 * g := by
        have e1 : (0 : ℝ) ≤ Cker ^ 2 * t * g :=
          mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt ht0)) (le_of_lt hg0)
        have e2 : (0 : ℝ) ≤ (2 * Cker + Cdiag) * t ^ 2 * g := by
          have : (0 : ℝ) ≤ 2 * Cker + Cdiag := by positivity
          exact mul_nonneg (mul_nonneg this (sq_nonneg _)) (le_of_lt hg0)
        exact add_nonneg e1 e2
      calc CK * g + CK * g + Cdiag * t * g + g * CK * CK
          = 2 * (Cker * t) * g + Cdiag * t * g + g * (Cker * t) * (Cker * t) :=
            hstep
        _ ≤ (2 * (Cker * t) * g + Cdiag * t * g + g * (Cker * t) * (Cker * t)) +
            (Cker ^ 2 * t * g + (2 * Cker + Cdiag) * t ^ 2 * g) :=
            le_add_of_nonneg_right hextra
        _ = (2 * Cker + Cdiag + Cker ^ 2) * t * g * (1 + t) := by ring
    calc p⁻¹ * |tangentProjection S D i j -
          D i j * tangentCoordinateKernel S i j i j|
        ≤ p⁻¹ * (CK * g + CK * g + Cdiag * t * g + g * CK * CK) :=
          mul_le_mul_of_nonneg_left habs (le_of_lt hpinv0)
      _ ≤ p⁻¹ * ((2 * Cker + Cdiag + Cker ^ 2) * t * g * (1 + t)) :=
          mul_le_mul_of_nonneg_left harith (le_of_lt hpinv0)
      _ = (2 * Cker + Cdiag + Cker ^ 2) * p⁻¹ * t * g * (1 + t) := by ring
  -- assemble the entry sup
  have hbound_eq : (2 * Cker + Cdiag + Cker ^ 2) * p⁻¹ *
      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
        (μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) *
          (1 + μ₀ * (r : ℝ) / (↑(min n₁ n₂))) =
      (2 * Cker + Cdiag + Cker ^ 2) * p⁻¹ * t * g * (1 + t) := by
    rw [ht_def, hg_def]
  rw [hbound_eq]
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => hFentry i j

