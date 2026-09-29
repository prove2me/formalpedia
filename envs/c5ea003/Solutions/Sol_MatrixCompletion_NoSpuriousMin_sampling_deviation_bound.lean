-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.sampling_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-13T19:36:24.747633+00:00
-- url     : https://prove2.me/submissions/bb45e5d7-8a7e-43fc-8895-3e0da67be915

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix Finset MatrixCompletion.NoSpuriousMin WithLp

namespace SampDevAux

variable {d : ℕ}

/-! ### `vecNorm` is the Euclidean norm -/

lemma vecNorm_nonneg (x : Fin d → ℝ) : 0 ≤ vecNorm x := Real.sqrt_nonneg _

lemma vecNorm_eq_norm (x : Fin d → ℝ) :
    vecNorm x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq, vecNorm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp [sq_abs]

lemma vecNorm_sq (x : Fin d → ℝ) : vecNorm x ^ 2 = ∑ i, x i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma inner_toLp' (x y : Fin d → ℝ) :
    (inner ℝ (toLp 2 x : EuclideanSpace ℝ (Fin d)) (toLp 2 y) : ℝ) = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct_comm]

/-- Cauchy–Schwarz for the dot product. -/
lemma abs_dotProduct_le (x y : Fin d → ℝ) : |x ⬝ᵥ y| ≤ vecNorm x * vecNorm y := by
  have h := abs_real_inner_le_norm (toLp 2 x : EuclideanSpace ℝ (Fin d)) (toLp 2 y)
  rwa [inner_toLp', ← vecNorm_eq_norm, ← vecNorm_eq_norm] at h

lemma vecNorm_smul (c : ℝ) (x : Fin d → ℝ) : vecNorm (c • x) = |c| * vecNorm x := by
  rw [vecNorm_eq_norm, vecNorm_eq_norm,
    show (toLp 2 (c • x) : EuclideanSpace ℝ (Fin d)) = c • toLp 2 x from rfl,
    norm_smul, Real.norm_eq_abs]

lemma eq_zero_of_vecNorm_eq_zero {x : Fin d → ℝ} (h : vecNorm x = 0) : x = 0 := by
  have h2 : ∑ i, x i ^ 2 = 0 := by rw [← vecNorm_sq, h]; ring
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).mp h2 i (Finset.mem_univ i)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-! ### The operator bound behind `sigmaMax` -/

/-- On the unit sphere `‖A v‖` never exceeds the Frobenius norm, so the supremum
defining `sigmaMax` is over a bounded set. -/
lemma vecNorm_mulVec_le_frob (A : Matrix (Fin d) (Fin d) ℝ) {v : Fin d → ℝ}
    (hv : vecNorm v = 1) : vecNorm (A *ᵥ v) ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
  have hv2 : ∑ j, v j ^ 2 = 1 := by rw [← vecNorm_sq, hv]; norm_num
  rw [vecNorm]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, (A *ᵥ v) i ^ 2
      ≤ ∑ i, (∑ j, A i j ^ 2) * ∑ j, v j ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [Matrix.mulVec, dotProduct] using
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) v
    _ = ∑ i, ∑ j, A i j ^ 2 := by simp [hv2]

lemma bddAbove_sigma (A : Matrix (Fin d) (Fin d) ℝ) :
    BddAbove (Set.range fun v : {v : Fin d → ℝ // vecNorm v = 1} => vecNorm (A.mulVec v.1)) := by
  refine ⟨Real.sqrt (∑ i, ∑ j, A i j ^ 2), ?_⟩
  rintro z ⟨v, rfl⟩
  exact vecNorm_mulVec_le_frob A v.2

lemma sigmaMax_nonneg (A : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ sigmaMax A :=
  Real.iSup_nonneg fun _ => vecNorm_nonneg _

lemma vecNorm_mulVec_le (A : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    vecNorm (A *ᵥ y) ≤ sigmaMax A * vecNorm y := by
  rcases eq_or_ne (vecNorm y) 0 with h | h
  · rw [eq_zero_of_vecNorm_eq_zero h, Matrix.mulVec_zero]
    simp [vecNorm]
  · have hy : 0 < vecNorm y := lt_of_le_of_ne (vecNorm_nonneg y) (Ne.symm h)
    have hu1 : vecNorm ((vecNorm y)⁻¹ • y) = 1 := by
      rw [vecNorm_smul, abs_of_pos (inv_pos.mpr hy), inv_mul_cancel₀ h]
    have hle : vecNorm (A *ᵥ ((vecNorm y)⁻¹ • y)) ≤ sigmaMax A :=
      le_ciSup (bddAbove_sigma A) (⟨(vecNorm y)⁻¹ • y, hu1⟩ : {v : Fin d → ℝ // vecNorm v = 1})
    rw [Matrix.mulVec_smul, vecNorm_smul, abs_of_pos (inv_pos.mpr hy)] at hle
    calc vecNorm (A *ᵥ y) = vecNorm y * ((vecNorm y)⁻¹ * vecNorm (A *ᵥ y)) := by field_simp
      _ ≤ vecNorm y * sigmaMax A := mul_le_mul_of_nonneg_left hle hy.le
      _ = sigmaMax A * vecNorm y := mul_comm _ _

lemma abs_bilin_le (A : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    |x ⬝ᵥ (A *ᵥ y)| ≤ sigmaMax A * vecNorm x * vecNorm y := by
  calc |x ⬝ᵥ (A *ᵥ y)| ≤ vecNorm x * vecNorm (A *ᵥ y) := abs_dotProduct_le _ _
    _ ≤ vecNorm x * (sigmaMax A * vecNorm y) :=
        mul_le_mul_of_nonneg_left (vecNorm_mulVec_le A y) (vecNorm_nonneg x)
    _ = sigmaMax A * vecNorm x * vecNorm y := by ring

/-! ### `sampDev` as a sum of bilinear forms in the centred sampling matrix -/

/-- The centred sampling matrix `Ω − t J`. -/
noncomputable def cent (Ω : Finset (Fin d × Fin d)) (t : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  sampMatrix Ω - t • Matrix.of fun _ _ => (1 : ℝ)

lemma sampDev_eq_sum (Ω : Finset (Fin d × Fin d)) (t : ℝ) (X Y : Matrix (Fin d) (Fin d) ℝ) :
    sampDev Ω t X Y = ∑ i, ∑ j, cent Ω t i j * (X i j * Y i j) := by
  simp only [sampDev, innerM, projSet, cent, sampMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_one, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option linter.unnecessarySeqFocus false in
  by_cases h : (i, j) ∈ Ω <;> simp [h] <;> ring

variable {r₁ r₂ : ℕ}

lemma sampDev_mul_transpose (Ω : Finset (Fin d × Fin d)) (t : ℝ)
    (A : Matrix (Fin d) (Fin r₁) ℝ) (B : Matrix (Fin d) (Fin r₂) ℝ)
    (C : Matrix (Fin d) (Fin r₁) ℝ) (D : Matrix (Fin d) (Fin r₂) ℝ) :
    sampDev Ω t (A * Cᵀ) (B * Dᵀ)
      = ∑ p : Fin r₁ × Fin r₂,
          (fun i => A i p.1 * B i p.2) ⬝ᵥ (cent Ω t *ᵥ fun j => C j p.1 * D j p.2) := by
  rw [sampDev_eq_sum, Fintype.sum_prod_type]
  have hL : ∀ i j : Fin d, cent Ω t i j * ((A * Cᵀ) i j * (B * Dᵀ) i j)
      = ∑ a, ∑ b, cent Ω t i j * (A i a * B i b) * (C j a * D j b) := by
    intro i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Matrix.transpose_apply]
    ring
  have hR : ∀ (a : Fin r₁) (b : Fin r₂),
      (fun i => A i a * B i b) ⬝ᵥ (cent Ω t *ᵥ fun j => C j a * D j b)
        = ∑ i, ∑ j, cent Ω t i j * (A i a * B i b) * (C j a * D j b) := by
    intro a b
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [hL, hR]
  calc ∑ i, ∑ j, ∑ a, ∑ b, cent Ω t i j * (A i a * B i b) * (C j a * D j b)
      = ∑ i, ∑ a, ∑ j, ∑ b, cent Ω t i j * (A i a * B i b) * (C j a * D j b) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, cent Ω t i j * (A i a * B i b) * (C j a * D j b) := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, cent Ω t i j * (A i a * B i b) * (C j a * D j b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, cent Ω t i j * (A i a * B i b) * (C j a * D j b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- Summing the squared norms of the entrywise row products recovers the product of row norms. -/
lemma sum_sq_vecNorm_pair (A : Matrix (Fin d) (Fin r₁) ℝ) (B : Matrix (Fin d) (Fin r₂) ℝ) :
    ∑ p : Fin r₁ × Fin r₂, vecNorm (fun i => A i p.1 * B i p.2) ^ 2
      = ∑ k, vecNorm (A k) ^ 2 * vecNorm (B k) ^ 2 := by
  simp only [vecNorm_sq, Fintype.sum_prod_type]
  calc ∑ a, ∑ b, ∑ i, (A i a * B i b) ^ 2
      = ∑ a, ∑ i, ∑ b, (A i a * B i b) ^ 2 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, (A i a * B i b) ^ 2 := Finset.sum_comm
    _ = ∑ k, (∑ a, A k a ^ 2) * ∑ b, B k b ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

end SampDevAux

open SampDevAux

theorem solution {d r₁ r₂ : ℕ} (Ω : Finset (Fin d × Fin d)) (t : ℝ)
    (A : Matrix (Fin d) (Fin r₁) ℝ) (B : Matrix (Fin d) (Fin r₂) ℝ)
    (C : Matrix (Fin d) (Fin r₁) ℝ) (D : Matrix (Fin d) (Fin r₂) ℝ) :
    |sampDev Ω t (A * Cᵀ) (B * Dᵀ)| ≤
      sampDevNorm Ω t
        * Real.sqrt (∑ k, vecNorm (A k) ^ 2 * vecNorm (B k) ^ 2)
        * Real.sqrt (∑ k, vecNorm (C k) ^ 2 * vecNorm (D k) ^ 2) := by
  classical
  have hsdn : sampDevNorm Ω t = sigmaMax (cent Ω t) := rfl
  -- Cauchy–Schwarz over the pairs of column indices.
  have hCS : ∑ p : Fin r₁ × Fin r₂,
        vecNorm (fun i => A i p.1 * B i p.2) * vecNorm (fun j => C j p.1 * D j p.2)
      ≤ Real.sqrt (∑ p : Fin r₁ × Fin r₂, vecNorm (fun i => A i p.1 * B i p.2) ^ 2)
        * Real.sqrt (∑ p : Fin r₁ × Fin r₂, vecNorm (fun j => C j p.1 * D j p.2) ^ 2) := by
    have hsq := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin r₁ × Fin r₂))
      (r := fun p => vecNorm (fun i => A i p.1 * B i p.2) * vecNorm (fun j => C j p.1 * D j p.2))
      (f := fun p => vecNorm (fun i => A i p.1 * B i p.2) ^ 2)
      (g := fun p => vecNorm (fun j => C j p.1 * D j p.2) ^ 2)
      (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _) (fun _ _ => le_of_eq (mul_pow _ _ 2))
    have hnn : 0 ≤ ∑ p : Fin r₁ × Fin r₂,
        vecNorm (fun i => A i p.1 * B i p.2) * vecNorm (fun j => C j p.1 * D j p.2) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    calc ∑ p : Fin r₁ × Fin r₂,
            vecNorm (fun i => A i p.1 * B i p.2) * vecNorm (fun j => C j p.1 * D j p.2)
        = Real.sqrt ((∑ p : Fin r₁ × Fin r₂, vecNorm (fun i => A i p.1 * B i p.2)
            * vecNorm (fun j => C j p.1 * D j p.2)) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  rw [sampDev_mul_transpose, hsdn]
  calc |∑ p : Fin r₁ × Fin r₂,
          (fun i => A i p.1 * B i p.2) ⬝ᵥ (cent Ω t *ᵥ fun j => C j p.1 * D j p.2)|
      ≤ ∑ p : Fin r₁ × Fin r₂,
          |(fun i => A i p.1 * B i p.2) ⬝ᵥ (cent Ω t *ᵥ fun j => C j p.1 * D j p.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : Fin r₁ × Fin r₂, sigmaMax (cent Ω t)
          * vecNorm (fun i => A i p.1 * B i p.2) * vecNorm (fun j => C j p.1 * D j p.2) :=
        Finset.sum_le_sum fun p _ => abs_bilin_le _ _ _
    _ = sigmaMax (cent Ω t) * ∑ p : Fin r₁ × Fin r₂,
          vecNorm (fun i => A i p.1 * B i p.2) * vecNorm (fun j => C j p.1 * D j p.2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ sigmaMax (cent Ω t)
          * (Real.sqrt (∑ p : Fin r₁ × Fin r₂, vecNorm (fun i => A i p.1 * B i p.2) ^ 2)
            * Real.sqrt (∑ p : Fin r₁ × Fin r₂, vecNorm (fun j => C j p.1 * D j p.2) ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS (sigmaMax_nonneg _)
    _ = sigmaMax (cent Ω t) * Real.sqrt (∑ k, vecNorm (A k) ^ 2 * vecNorm (B k) ^ 2)
          * Real.sqrt (∑ k, vecNorm (C k) ^ 2 * vecNorm (D k) ^ 2) := by
        rw [sum_sq_vecNorm_pair, sum_sq_vecNorm_pair]
        ring
