-- Prove2me | solution 2 for tangent_diagonal_multiplier_sign_spectral_norm_bound_from_a1
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T17:03:24.352993+00:00
-- url     : https://prove2.me/submissions/66f8837c-a359-4355-8b3c-0a33ccbf95b4

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.CStarAlgebra.Matrix

open MatrixCompletion
open scoped BigOperators Matrix.Norms.L2Operator

namespace Bot2DiagMult

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- Column projector diagonal energy `pu i = ∑_k u_k(i)²`. -/
noncomputable def pu (S : SVD M r) (i : Fin n1) : Real := ∑ k : Fin r, S.u k i ^ 2

/-- Row projector diagonal energy `pv j = ∑_k v_k(j)²`. -/
noncomputable def pv (S : SVD M r) (j : Fin n2) : Real := ∑ k : Fin r, S.v k j ^ 2

/-- `spectralNorm` is exactly the l2 operator norm of the matrix. -/
lemma spectralNorm_eq_l2 {a b : Nat} (X : RealMatrix a b) :
    spectralNorm X = ‖X‖ := by
  rw [spectralNorm, Matrix.l2_opNorm_def]; rfl

/-- The diagonal tangent kernel evaluates to `pu i + pv j − pu i · pv j` (CR eq. 6.11). -/
lemma kernel_diag (S : SVD M r) (i : Fin n1) (j : Fin n2) :
    tangentCoordinateKernel S i j i j = pu S i + pv S j - pu S i * pv S j := by
  unfold tangentCoordinateKernel matrixInner tangentProjection
  -- inner product with e_ij extracts entry (i,j)
  have hpick : ∀ (Y : RealMatrix n1 n2),
      (∑ a : Fin n1, ∑ b : Fin n2,
        Y a b * coordinateMatrix i j a b) = Y i j := by
    intro Y
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp [coordinateMatrix]
      · intro b _ hb; simp [coordinateMatrix, hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    · intro a _ ha
      apply Finset.sum_eq_zero; intro b _; simp [coordinateMatrix, ha]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hpick]
  -- now evaluate (left + right - two) at (i,j)
  simp only [Matrix.sub_apply, Matrix.add_apply]
  unfold leftSingularProjection rightSingularProjection twoSidedSingularProjection
  -- left at (i,j): ∑ a (∑ k u k i u k a) * e_ij a j = (∑ k u k i u k i)
  have hL : (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * coordinateMatrix i j a j)
      = pu S i := by
    rw [Finset.sum_eq_single i]
    · simp only [coordinateMatrix, and_self, if_true, mul_one]; unfold pu
      exact Finset.sum_congr rfl (fun k _ => by ring)
    · intro a _ ha; simp [coordinateMatrix, ha]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hR : (∑ b : Fin n2, coordinateMatrix i j i b * (∑ k : Fin r, S.v k b * S.v k j))
      = pv S j := by
    rw [Finset.sum_eq_single j]
    · simp only [coordinateMatrix, and_self, if_true, one_mul]; unfold pv
      exact Finset.sum_congr rfl (fun k _ => by ring)
    · intro b _ hb; simp [coordinateMatrix, hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hT : (∑ a : Fin n1, ∑ b : Fin n2,
        (∑ k : Fin r, S.u k i * S.u k a) * coordinateMatrix i j a b *
          (∑ l : Fin r, S.v l b * S.v l j)) = pu S i * pv S j := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp only [coordinateMatrix, and_self, if_true, mul_one]
        unfold pu pv
        rw [Finset.sum_congr rfl (fun k _ => (sq (S.u k i)).symm),
            Finset.sum_congr rfl (fun k _ => (sq (S.v k j)).symm)]
      · intro b _ hb; simp [coordinateMatrix, hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [coordinateMatrix, ha]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hL, hR, hT]

/-- Entry of the sign matrix: `E_{ij} = ∑_k u_k(i) v_k(j)`. -/
lemma signMatrix_apply (S : SVD M r) (i : Fin n1) (j : Fin n2) :
    signMatrix S i j = ∑ k : Fin r, S.u k i * S.v k j := by
  unfold signMatrix
  rw [Matrix.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => by simp [Matrix.vecMulVec_apply])

/-- Row-energy identity: `pu i = ∑_j E_{ij}²`. -/
lemma pu_eq_rowEnergy (S : SVD M r) (i : Fin n1) :
    pu S i = ∑ j : Fin n2, (signMatrix S i j) ^ 2 := by
  have expand : ∀ j : Fin n2, (signMatrix S i j) ^ 2
      = ∑ k : Fin r, ∑ l : Fin r, S.u k i * S.u l i * (S.v k j * S.v l j) := by
    intro j
    rw [signMatrix_apply, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  rw [Finset.sum_congr rfl (fun j _ => expand j)]
  rw [Finset.sum_comm]  -- bring j outermost? actually swap to sum over k,l first
  -- ∑_j ∑_k ∑_l  ->  ∑_k ∑_l ∑_j
  have hswap : (∑ j : Fin n2, ∑ k : Fin r, ∑ l : Fin r,
        S.u k i * S.u l i * (S.v k j * S.v l j))
      = ∑ k : Fin r, ∑ l : Fin r, S.u k i * S.u l i * (∑ j : Fin n2, S.v k j * S.v l j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [show (∑ k : Fin r, ∑ j : Fin n2, ∑ l : Fin r,
        S.u k i * S.u l i * (S.v k j * S.v l j))
      = ∑ j : Fin n2, ∑ k : Fin r, ∑ l : Fin r,
        S.u k i * S.u l i * (S.v k j * S.v l j) from (Finset.sum_comm)]
  rw [hswap]
  have orth : ∀ k l : Fin r, (∑ j : Fin n2, S.v k j * S.v l j) = if k = l then 1 else 0 :=
    S.v_orthonormal
  rw [Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun l _ => by rw [orth k l]))]
  unfold pu
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · simp [sq]
  · intro l _ hl; simp [hl, Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Column-energy identity: `pv j = ∑_i E_{ij}²`. -/
lemma pv_eq_colEnergy (S : SVD M r) (j : Fin n2) :
    pv S j = ∑ i : Fin n1, (signMatrix S i j) ^ 2 := by
  have expand : ∀ i : Fin n1, (signMatrix S i j) ^ 2
      = ∑ k : Fin r, ∑ l : Fin r, S.v k j * S.v l j * (S.u k i * S.u l i) := by
    intro i
    rw [signMatrix_apply, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  rw [Finset.sum_congr rfl (fun i _ => expand i)]
  have hswap : (∑ i : Fin n1, ∑ k : Fin r, ∑ l : Fin r,
        S.v k j * S.v l j * (S.u k i * S.u l i))
      = ∑ k : Fin r, ∑ l : Fin r, S.v k j * S.v l j * (∑ i : Fin n1, S.u k i * S.u l i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [hswap]
  have orth : ∀ k l : Fin r, (∑ i : Fin n1, S.u k i * S.u l i) = if k = l then 1 else 0 :=
    S.u_orthonormal
  rw [Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun l _ => by rw [orth k l]))]
  unfold pv
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · simp [sq]
  · intro l _ hl; simp [hl, Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- A1 gives the entry-square bound `E_{ij}² ≤ μ₁² r / (n₁ n₂)`. -/
lemma sq_entry_bound (S : SVD M r) (μ1 : Real) (hμ : A1 S μ1)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (i : Fin n1) (j : Fin n2) :
    (signMatrix S i j) ^ 2 ≤ μ1 ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real)) := by
  have h := hμ i j
  have hnn : (0:Real) ≤ Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real))) := Real.sqrt_nonneg _
  -- |E_ij|^2 ≤ (μ1 * sqrt(r/(n1 n2)))^2
  have hsq : (signMatrix S i j) ^ 2 ≤ (μ1 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real)))) ^ 2 := by
    rw [← sq_abs (signMatrix S i j)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hpos : (0:Real) < (n1 : Real) * (n2 : Real) := by positivity
  have hrhs : (μ1 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real)))) ^ 2
      = μ1 ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hrhs] at hsq; exact hsq

/-- A1 row-energy bound: `pu i ≤ μ₁² r / n₁`. -/
lemma pu_bound (S : SVD M r) (μ1 : Real) (hμ : A1 S μ1)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (i : Fin n1) :
    pu S i ≤ μ1 ^ 2 * (r : Real) / (n1 : Real) := by
  rw [pu_eq_rowEnergy]
  calc ∑ j : Fin n2, (signMatrix S i j) ^ 2
      ≤ ∑ _j : Fin n2, μ1 ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real)) :=
        Finset.sum_le_sum (fun j _ => sq_entry_bound S μ1 hμ hn1 hn2 i j)
    _ = (n2 : Real) * (μ1 ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = μ1 ^ 2 * (r : Real) / (n1 : Real) := by
        have h2 : (n2:Real) ≠ 0 := by positivity
        field_simp

/-- A1 column-energy bound: `pv j ≤ μ₁² r / n₂`. -/
lemma pv_bound (S : SVD M r) (μ1 : Real) (hμ : A1 S μ1)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (j : Fin n2) :
    pv S j ≤ μ1 ^ 2 * (r : Real) / (n2 : Real) := by
  rw [pv_eq_colEnergy]
  calc ∑ i : Fin n1, (signMatrix S i j) ^ 2
      ≤ ∑ _i : Fin n1, μ1 ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real)) :=
        Finset.sum_le_sum (fun i _ => sq_entry_bound S μ1 hμ hn1 hn2 i j)
    _ = (n1 : Real) * (μ1 ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = μ1 ^ 2 * (r : Real) / (n2 : Real) := by
        have h1 : (n1:Real) ≠ 0 := by positivity
        field_simp

/-- `pu`/`pv` are nonnegative (sums of squares). -/
lemma pu_nonneg (S : SVD M r) (i : Fin n1) : 0 ≤ pu S i := by
  unfold pu; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
lemma pv_nonneg (S : SVD M r) (j : Fin n2) : 0 ≤ pv S j := by
  unfold pv; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

/-- CR eq. (6.11): `D_T(E) = Λ_U · E · (1 − Λ_V) + E · Λ_V`, two-sided diagonal
multiplication. Here `Λ_U = diagonal pu`, `Λ_V = diagonal pv`. -/
lemma factor (S : SVD M r) :
    tangentDiagonalMultiplier S (signMatrix S)
      = Matrix.diagonal (pu S) * signMatrix S * (1 - Matrix.diagonal (pv S))
        + signMatrix S * Matrix.diagonal (pv S) := by
  funext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, tangentDiagonalMultiplier]
  rw [kernel_diag]
  -- evaluate the two matrix products at (i,j)
  have hLE : (∑ a : Fin n1, Matrix.diagonal (pu S) i a * signMatrix S a j) = pu S i * signMatrix S i j := by
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal]
    · intro a _ ha; simp [Matrix.diagonal, Ne.symm ha]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- (Λ_U E)(1-Λ_V) at (i,j) = (Λ_U E)_{ij} * (1-Λ_V)_{jj}
  have hRdiag : (∑ b : Fin n2, (∑ a : Fin n1, Matrix.diagonal (pu S) i a * signMatrix S a b)
        * (1 - Matrix.diagonal (pv S)) b j)
      = (pu S i * signMatrix S i j) * (1 - pv S j) := by
    rw [Finset.sum_eq_single j]
    · rw [show (∑ a : Fin n1, Matrix.diagonal (pu S) i a * signMatrix S a j) = pu S i * signMatrix S i j from hLE]
      simp [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal]
    · intro b _ hb
      simp [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal, hb, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hER : (∑ b : Fin n2, signMatrix S i b * Matrix.diagonal (pv S) b j) = signMatrix S i j * pv S j := by
    rw [Finset.sum_eq_single j]
    · simp [Matrix.diagonal]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne (pv S) hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hRdiag, hER]; ring

/-- Norm of the diagonal `Λ_U` is `‖pu‖` (the Pi sup norm), bounded by `μ₁² r / n₁`. -/
lemma norm_diag_pu_le (S : SVD M r) (μ1 : Real) (hμ : A1 S μ1)
    (hn1 : 0 < n1) (hn2 : 0 < n2) :
    ‖(Matrix.diagonal (pu S) : Matrix (Fin n1) (Fin n1) Real)‖ ≤ μ1 ^ 2 * (r : Real) / (n1 : Real) := by
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pu_nonneg S i)]
  exact pu_bound S μ1 hμ hn1 hn2 i

lemma norm_diag_pv_le (S : SVD M r) (μ1 : Real) (hμ : A1 S μ1)
    (hn1 : 0 < n1) (hn2 : 0 < n2) :
    ‖(Matrix.diagonal (pv S) : Matrix (Fin n2) (Fin n2) Real)‖ ≤ μ1 ^ 2 * (r : Real) / (n2 : Real) := by
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pv_nonneg S j)]
  exact pv_bound S μ1 hμ hn1 hn2 j

/-- `pv j = (P_V)_{jj} ≤ 1`: a projection diagonal entry. Proof via idempotence
`t = ∑_{j'} (P_V)_{jj'}² ≥ t²` with `t = pv j ≥ 0`. -/
lemma pv_le_one (S : SVD M r) (j : Fin n2) : pv S j ≤ 1 := by
  set t := pv S j with ht
  have htnn : 0 ≤ t := pv_nonneg S j
  -- (P_V)_{j j'} := ∑_k v_k j * v_k j'.  Then t = (P_V)_{jj}.
  have hidem : t = ∑ j' : Fin n2, (∑ k : Fin r, S.v k j * S.v k j') ^ 2 := by
    rw [ht]; unfold pv
    -- ∑_{j'} (∑_k v_k j v_k j')² = ∑_k v_k j² by orthonormality (same computation as pv_eq_colEnergy)
    have expand : ∀ j' : Fin n2, (∑ k : Fin r, S.v k j * S.v k j') ^ 2
        = ∑ k : Fin r, ∑ l : Fin r, S.v k j * S.v l j * (S.v k j' * S.v l j') := by
      intro j'
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    rw [Finset.sum_congr rfl (fun j' _ => expand j')]
    have hswap : (∑ j' : Fin n2, ∑ k : Fin r, ∑ l : Fin r,
          S.v k j * S.v l j * (S.v k j' * S.v l j'))
        = ∑ k : Fin r, ∑ l : Fin r, S.v k j * S.v l j * (∑ j' : Fin n2, S.v k j' * S.v l j') := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_); rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_); rw [Finset.mul_sum]
    rw [hswap]
    have orth : ∀ k l : Fin r, (∑ j' : Fin n2, S.v k j' * S.v l j') = if k = l then 1 else 0 :=
      S.v_orthonormal
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by rw [orth k l]))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_eq_single k]
    · simp [sq]
    · intro l _ hl; simp [Ne.symm hl]
    · intro h; exact absurd (Finset.mem_univ k) h
  -- t = (diagonal term) + (rest) ≥ t² since (P_V)_{jj} = ∑_k v_k j² = t
  have hdiag : (∑ k : Fin r, S.v k j * S.v k j) = t := by
    rw [ht]; unfold pv; exact Finset.sum_congr rfl (fun k _ => by rw [sq])
  have hsq_le : t ^ 2 ≤ t := by
    have hsingle : (∑ k : Fin r, S.v k j * S.v k j) ^ 2 ≤
        ∑ j' : Fin n2, (∑ k : Fin r, S.v k j * S.v k j') ^ 2 := by
      refine Finset.single_le_sum (f := fun j' => (∑ k : Fin r, S.v k j * S.v k j') ^ 2)
        (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
    calc t ^ 2 = (∑ k : Fin r, S.v k j * S.v k j) ^ 2 := by rw [hdiag]
      _ ≤ ∑ j' : Fin n2, (∑ k : Fin r, S.v k j * S.v k j') ^ 2 := hsingle
      _ = t := hidem.symm
  -- t² ≤ t with t ≥ 0 ⟹ t ≤ 1
  nlinarith [hsq_le, htnn, sq_nonneg (t - 1)]

/-- `‖1 − Λ_V‖ ≤ 1` (entries of `pv` lie in `[0,1]`). -/
lemma norm_one_sub_diag_pv_le (S : SVD M r) :
    ‖(1 - Matrix.diagonal (pv S) : Matrix (Fin n2) (Fin n2) Real)‖ ≤ 1 := by
  have hdiff : (1 - Matrix.diagonal (pv S) : Matrix (Fin n2) (Fin n2) Real)
      = Matrix.diagonal (fun j => 1 - pv S j) := by
    funext a b
    by_cases hab : a = b
    · subst hab; simp [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal]
    · simp [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal, hab]
  rw [hdiff, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := pv_le_one S j; linarith
  · have := pv_nonneg S j; linarith

/-- **CR Lemma 6.4 (A1-effective form).** The diagonal tangent-kernel multiplier of
the sign matrix satisfies `‖D_T(E)‖ ≤ 2·(μ₁² r / min n₁ n₂)·‖E‖`. -/
theorem tangent_diagonal_multiplier_sign_spectral_norm_bound_from_a1 :
    ∃ Cdiag : Real, 0 < Cdiag ∧
      ∀ (n1 n2 r : Nat) (M : RealMatrix n1 n2) (μ1 : Real) (S : SVD M r),
        0 < n1 → 0 < n2 → 0 < r → 1 ≤ μ1 → A1 S μ1 →
        spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
          Cdiag * (μ1 ^ 2 * (r : Real) / (↑(min n1 n2))) *
            spectralNorm (signMatrix S) := by
  refine ⟨2, by norm_num, ?_⟩
  intro n1 n2 r M μ1 S hn1 hn2 hr hμ1 hA1
  rw [spectralNorm_eq_l2, spectralNorm_eq_l2, factor]
  set E : Matrix (Fin n1) (Fin n2) Real := signMatrix S with hE
  set ΛU : Matrix (Fin n1) (Fin n1) Real := Matrix.diagonal (pu S) with hΛU
  set ΛV : Matrix (Fin n2) (Fin n2) Real := Matrix.diagonal (pv S) with hΛV
  have hEnn : 0 ≤ ‖E‖ := norm_nonneg _
  -- triangle inequality
  have htri : ‖ΛU * E * (1 - ΛV) + E * ΛV‖ ≤ ‖ΛU * E * (1 - ΛV)‖ + ‖E * ΛV‖ := norm_add_le _ _
  -- submultiplicativity on each term
  have hT1 : ‖ΛU * E * (1 - ΛV)‖ ≤ ‖ΛU‖ * ‖E‖ * ‖1 - ΛV‖ := by
    calc ‖ΛU * E * (1 - ΛV)‖ ≤ ‖ΛU * E‖ * ‖1 - ΛV‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖ΛU‖ * ‖E‖) * ‖1 - ΛV‖ := by
          apply mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
  have hT2 : ‖E * ΛV‖ ≤ ‖E‖ * ‖ΛV‖ := Matrix.l2_opNorm_mul _ _
  -- bound the factor norms
  have hbU : ‖ΛU‖ ≤ μ1 ^ 2 * (r : Real) / (n1 : Real) := norm_diag_pu_le S μ1 hA1 hn1 hn2
  have hbV : ‖ΛV‖ ≤ μ1 ^ 2 * (r : Real) / (n2 : Real) := norm_diag_pv_le S μ1 hA1 hn1 hn2
  have hb1V : ‖(1 - ΛV : Matrix (Fin n2) (Fin n2) Real)‖ ≤ 1 := norm_one_sub_diag_pv_le S
  have hUnn : 0 ≤ ‖ΛU‖ := norm_nonneg _
  have hVnn : 0 ≤ ‖ΛV‖ := norm_nonneg _
  have h1Vnn : 0 ≤ ‖(1 - ΛV : Matrix (Fin n2) (Fin n2) Real)‖ := norm_nonneg _
  -- combine: term1 ≤ (μ₁²r/n₁)·‖E‖·1, term2 ≤ ‖E‖·(μ₁²r/n₂)
  have hUrnn : 0 ≤ μ1 ^ 2 * (r : Real) / (n1 : Real) := by positivity
  have hVrnn : 0 ≤ μ1 ^ 2 * (r : Real) / (n2 : Real) := by positivity
  have hterm1 : ‖ΛU * E * (1 - ΛV)‖ ≤ (μ1 ^ 2 * (r : Real) / (n1 : Real)) * ‖E‖ := by
    calc ‖ΛU * E * (1 - ΛV)‖ ≤ ‖ΛU‖ * ‖E‖ * ‖1 - ΛV‖ := hT1
      _ ≤ (μ1 ^ 2 * (r : Real) / (n1 : Real)) * ‖E‖ * 1 := by
          gcongr
      _ = (μ1 ^ 2 * (r : Real) / (n1 : Real)) * ‖E‖ := by ring
  have hterm2 : ‖E * ΛV‖ ≤ ‖E‖ * (μ1 ^ 2 * (r : Real) / (n2 : Real)) := by
    calc ‖E * ΛV‖ ≤ ‖E‖ * ‖ΛV‖ := hT2
      _ ≤ ‖E‖ * (μ1 ^ 2 * (r : Real) / (n2 : Real)) := by gcongr
  -- min bounds: 1/n1 ≤ 1/min, 1/n2 ≤ 1/min
  have hmin1 : (μ1 ^ 2 * (r : Real) / (n1 : Real)) ≤ μ1 ^ 2 * (r : Real) / (↑(min n1 n2)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.cast_le.mpr (Nat.min_le_left n1 n2)
  have hmin2 : (μ1 ^ 2 * (r : Real) / (n2 : Real)) ≤ μ1 ^ 2 * (r : Real) / (↑(min n1 n2)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.cast_le.mpr (Nat.min_le_right n1 n2)
  -- assemble
  calc ‖ΛU * E * (1 - ΛV) + E * ΛV‖
      ≤ ‖ΛU * E * (1 - ΛV)‖ + ‖E * ΛV‖ := htri
    _ ≤ (μ1 ^ 2 * (r : Real) / (n1 : Real)) * ‖E‖ + ‖E‖ * (μ1 ^ 2 * (r : Real) / (n2 : Real)) :=
        add_le_add hterm1 hterm2
    _ ≤ (μ1 ^ 2 * (r : Real) / (↑(min n1 n2))) * ‖E‖ + ‖E‖ * (μ1 ^ 2 * (r : Real) / (↑(min n1 n2))) := by
        gcongr
    _ = 2 * (μ1 ^ 2 * (r : Real) / (↑(min n1 n2))) * ‖E‖ := by ring

end Bot2DiagMult



open Bot2DiagMult

theorem solution :
    ∃ Cdiag : ℝ, 0 < Cdiag ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₁ → A1 S μ₁ →
        spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
          Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm (signMatrix S) :=
  Bot2DiagMult.tangent_diagonal_multiplier_sign_spectral_norm_bound_from_a1
