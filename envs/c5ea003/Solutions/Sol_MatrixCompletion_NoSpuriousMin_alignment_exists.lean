-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.alignment_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-13T19:27:04.082985+00:00
-- url     : https://prove2.me/submissions/2bd9ed54-3c5d-42ed-8d82-1b16a5c9b201

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

open Matrix Finset WithLp

namespace Polar

variable {r : ℕ}

lemma conjTranspose_real (A : Matrix (Fin r) (Fin r) ℝ) : Aᴴ = Aᵀ := by
  ext i j; simp [Matrix.conjTranspose_apply]

/-- The Euclidean inner product of two `toLp`-transported vectors is their dot product. -/
lemma inner_toLp (x y : Fin r → ℝ) : (inner ℝ (toLp 2 x) (toLp 2 y) : ℝ) = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct_comm]

/-- `⟪M x, M y⟫ = ⟪x, MᵀM y⟫`. -/
lemma dotProduct_mulVec_mulVec (M : Matrix (Fin r) (Fin r) ℝ) (x y : Fin r → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ ((Mᵀ * M) *ᵥ y) := by
  conv_rhs => rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- A square matrix whose columns are an orthonormal family is orthogonal. -/
lemma transpose_mul_self_of_orthonormal (B : Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ i j, (Bᵀ i) ⬝ᵥ (Bᵀ j) = if i = j then (1 : ℝ) else 0) :
    Bᵀ * B = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have := hB i j
  rw [dotProduct] at this
  simpa [Matrix.transpose_apply] using this

end Polar

open Polar

/-- **Polar-type decomposition.** For every real square matrix `M` there is an orthogonal `R`
with `M * R` positive semidefinite. -/
theorem exists_orthogonal_mul_posSemidef {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) :
    ∃ R : Matrix (Fin r) (Fin r) ℝ, R * Rᵀ = 1 ∧ (M * R).PosSemidef := by
  classical
  -- Spectral data of `S = Mᵀ M`.
  have hS : (Mᵀ * M).IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_self M
    rwa [conjTranspose_real] at h
  set e := hS.eigenvectorBasis with he
  set μ := hS.eigenvalues with hμ
  set v : Fin r → (Fin r → ℝ) := fun i => ofLp (e i) with hv
  -- The eigenvector equation and orthonormality of `v`.
  have heig : ∀ i, (Mᵀ * M) *ᵥ v i = μ i • v i := fun i => hS.mulVec_eigenvectorBasis i
  have hvorth : ∀ i j, v i ⬝ᵥ v j = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h := orthonormal_iff_ite.mp e.orthonormal i j
    rwa [show (e i) = toLp 2 (v i) by simp [hv], show (e j) = toLp 2 (v j) by simp [hv],
      inner_toLp] at h
  -- `⟪M vᵢ, M vⱼ⟫ = μⱼ δᵢⱼ`; in particular `‖M vᵢ‖² = μᵢ ≥ 0`.
  have hMv : ∀ i j, (M *ᵥ v i) ⬝ᵥ (M *ᵥ v j) = if i = j then μ j else 0 := by
    intro i j
    rw [dotProduct_mulVec_mulVec, heig j, dotProduct_smul, hvorth i j]
    by_cases h : i = j <;> simp [h]
  have hμnonneg : ∀ i, 0 ≤ μ i := by
    intro i
    have h : (M *ᵥ v i) ⬝ᵥ (M *ᵥ v i) = μ i := by simpa using hMv i i
    rw [← h]
    exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
  set σ : Fin r → ℝ := fun i => Real.sqrt (μ i) with hσ
  have hσsq : ∀ i, σ i ^ 2 = μ i := fun i => Real.sq_sqrt (hμnonneg i)
  have hσnonneg : ∀ i, 0 ≤ σ i := fun i => Real.sqrt_nonneg _
  -- The normalised images.
  set w : Fin r → (Fin r → ℝ) := fun i => (σ i)⁻¹ • (M *ᵥ v i) with hw
  set s : Set (Fin r) := {i | σ i ≠ 0} with hs
  -- On `s` the family `w` is orthonormal.
  have hworth : ∀ i ∈ s, ∀ j ∈ s, w i ⬝ᵥ w j = if i = j then (1 : ℝ) else 0 := by
    intro i hi j hj
    have hi' : σ i ≠ 0 := hi
    have hj' : σ j ≠ 0 := hj
    rw [hw]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hMv i j]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl, ← hσsq i]
      field_simp
    · simp [h]
  -- Extend `w|s` to an orthonormal basis of `EuclideanSpace ℝ (Fin r)`.
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) = Fintype.card (Fin r) := by simp
  have hworth' : Orthonormal ℝ (s.restrict fun i => toLp 2 (w i)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.restrict_apply, inner_toLp, hworth i hi j hj, Subtype.mk.injEq]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq (v := fun i => toLp 2 (w i))
      hcard hworth'
  -- `M vᵢ = σᵢ · bᵢ`, for every `i` (both sides vanish when `σᵢ = 0`).
  have hkey : ∀ i, M *ᵥ v i = σ i • ofLp (b i) := by
    intro i
    by_cases hi : i ∈ s
    · have hi' : σ i ≠ 0 := hi
      rw [hb i hi]
      simp only [hw, smul_smul, mul_inv_cancel₀ hi', one_smul]
    · have hi' : σ i = 0 := by simpa [hs] using hi
      have hμi : μ i = 0 := by rw [← hσsq i, hi']; ring
      have : (M *ᵥ v i) ⬝ᵥ (M *ᵥ v i) = 0 := by rw [hMv i i]; simp [hμi]
      have hzero : M *ᵥ v i = 0 := by
        funext k
        have hsum : ∑ l, (M *ᵥ v i) l * (M *ᵥ v i) l = 0 := this
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun l _ => mul_self_nonneg ((M *ᵥ v i) l))).mp hsum k (Finset.mem_univ k)
        simpa using mul_self_eq_zero.mp this
      rw [hzero, hi', zero_smul]
  -- Assemble the matrices: `V` has columns `vᵢ`, `B` has columns `bᵢ`.
  set V : Matrix (Fin r) (Fin r) ℝ := Matrix.of (fun k i => v i k) with hV
  set B : Matrix (Fin r) (Fin r) ℝ := Matrix.of (fun k i => (ofLp (b i)) k) with hB
  have hVorth : Vᵀ * V = 1 := by
    refine transpose_mul_self_of_orthonormal V fun i j => ?_
    simpa [hV, Matrix.transpose_apply] using hvorth i j
  have hBorth : Bᵀ * B = 1 := by
    refine transpose_mul_self_of_orthonormal B fun i j => ?_
    have h := orthonormal_iff_ite.mp b.orthonormal i j
    rwa [show (b i) = toLp 2 (ofLp (b i)) by simp,
      show (b j) = toLp 2 (ofLp (b j)) by simp, inner_toLp] at h
  have hBorth' : B * Bᵀ = 1 := mul_eq_one_comm.mp hBorth
  have hVorth' : V * Vᵀ = 1 := mul_eq_one_comm.mp hVorth
  -- `M V = B diag(σ)`.
  have hMV : M * V = B * Matrix.diagonal σ := by
    ext k i
    have := congrFun (hkey i) k
    simpa [hV, hB, Matrix.mul_apply, Matrix.diagonal, Matrix.mulVec, dotProduct,
      Finset.mul_sum, mul_comm] using this
  -- `R = V Bᵀ` is orthogonal and `M R = B diag(σ) Bᵀ` is positive semidefinite.
  refine ⟨V * Bᵀ, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
      Matrix.mul_assoc V Bᵀ B, hBorth, Matrix.mul_one, hVorth']
  · have hMR : M * (V * Bᵀ) = B * Matrix.diagonal σ * Bᵀ := by
      rw [← Matrix.mul_assoc, hMV]
    rw [hMR, ← conjTranspose_real B]
    exact (Matrix.PosSemidef.diagonal hσnonneg).mul_mul_conjTranspose_same B

theorem solution {d r : ℕ} (Z X : Matrix (Fin d) (Fin r) ℝ) :
    ∃ U : Matrix (Fin d) (Fin r) ℝ, U * Uᵀ = Z * Zᵀ ∧ (Xᵀ * U).PosSemidef := by
  obtain ⟨R, hR, hPSD⟩ := exists_orthogonal_mul_posSemidef (Xᵀ * Z)
  refine ⟨Z * R, ?_, ?_⟩
  · rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Z R, hR, Matrix.mul_one]
  · rwa [← Matrix.mul_assoc]
