-- Prove2me | solution 1 for ConvexOptimization.lowner_john_affine_invariant
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-15T15:05:20.271027+00:00
-- url     : https://prove2.me/submissions/6825a5a2-da46-420d-9cae-3235a55499d4

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn

open scoped RealInnerProductSpace ENNReal MatrixOrder
open MeasureTheory
open Matrix

namespace LJAux

open ConvexOptimization

variable {nn : ℕ}

theorem dot_mulVec_left (A : Matrix (Fin nn) (Fin nn) ℝ) (x y : Fin nn → ℝ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Symmetrization of an ellipsoid.** For invertible `M`, the set `{v | ‖Mv + c‖ ≤ 1}`
is the ellipsoid of a symmetric positive definite matrix `S` with `det S = |det M|`.
This is the polar decomposition `M = US` with `U` orthogonal. -/
theorem exists_symm_repr (M : Matrix (Fin nn) (Fin nn) ℝ) (hM : IsUnit M.det)
    (c : Fin nn → ℝ) :
    ∃ (S : Matrix (Fin nn) (Fin nn) ℝ) (d : Fin nn → ℝ),
      S.IsSymm ∧ S.PosDef ∧ S.det = |M.det| ∧ ellipsoidBody S d = ellipsoidBody M c := by
  classical
  have hPsd : (Mᵀ * M).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self M
  set S : Matrix (Fin nn) (Fin nn) ℝ := CFC.sqrt (Mᵀ * M) with hSdef
  have hSsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Mᵀ * M))
  have hSsq : S * S = Mᵀ * M := by
    have h := CFC.sq_sqrt (Mᵀ * M) (Matrix.nonneg_iff_posSemidef.mpr hPsd)
    rwa [sq] at h
  have hSsymm : S.IsSymm := hSsd.isHermitian
  have hPdet : (Mᵀ * M).det = M.det * M.det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
  have hSdetsq : S.det * S.det = M.det * M.det := by
    rw [← Matrix.det_mul, hSsq, hPdet]
  have hSdetnn : 0 ≤ S.det := hSsd.det_nonneg
  have hSdet : S.det = |M.det| := by
    have h1 : |S.det| = |M.det| := by
      have : |S.det| * |S.det| = |M.det| * |M.det| := by
        rw [← abs_mul, ← abs_mul, hSdetsq]
      nlinarith [abs_nonneg S.det, abs_nonneg M.det]
    rwa [abs_of_nonneg hSdetnn] at h1
  have hSdetne : S.det ≠ 0 := by
    rw [hSdet]
    exact abs_ne_zero.mpr hM.ne_zero
  have hSpd : S.PosDef := (Matrix.PosSemidef.posDef_iff_det_ne_zero hSsd).mpr hSdetne
  have hSunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdetne
  -- The orthogonal factor of the polar decomposition.
  set U : Matrix (Fin nn) (Fin nn) ℝ := M * S⁻¹ with hUdef
  have hSinvT : (S⁻¹)ᵀ = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hSsymm.eq]
  have hUU : Uᵀ * U = 1 := by
    have hassoc : Uᵀ * U = S⁻¹ * ((Mᵀ * M) * S⁻¹) := by
      rw [hUdef, Matrix.transpose_mul, hSinvT]
      simp [Matrix.mul_assoc]
    rw [hassoc, ← hSsq, Matrix.mul_assoc S S S⁻¹, Matrix.mul_nonsing_inv S hSunit,
      Matrix.mul_one, Matrix.nonsing_inv_mul S hSunit]
  have hUU' : U * Uᵀ = 1 := Matrix.mul_eq_one_comm.mp hUU
  have hUS : U * S = M := by
    rw [hUdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul S hSunit, Matrix.mul_one]
  set d : Fin nn → ℝ := Uᵀ *ᵥ c with hddef
  have hUd : U *ᵥ d = c := by
    rw [hddef, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  have hshift : ∀ w : Fin nn → ℝ, U *ᵥ (S *ᵥ w + d) = M *ᵥ w + c := by
    intro w
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hUS, hUd]
  have hiso : ∀ x : Fin nn → ℝ, (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
    intro x
    rw [dot_mulVec_left, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  refine ⟨S, d, hSsymm, hSpd, hSdet, ?_⟩
  ext w
  simp only [ellipsoidBody, Set.mem_setOf_eq, ← hshift w, hiso]

/-- Pushing an ellipsoid forward along an invertible affine map. -/
theorem image_ellipsoidBody (T A : Matrix (Fin nn) (Fin nn) ℝ) (hT : IsUnit T.det)
    (t b : Fin nn → ℝ) :
    (fun v => T *ᵥ v + t) '' ellipsoidBody A b
      = ellipsoidBody (A * T⁻¹) (b - (A * T⁻¹) *ᵥ t) := by
  have hkey : ∀ v : Fin nn → ℝ,
      (A * T⁻¹) *ᵥ (T *ᵥ v + t) + (b - (A * T⁻¹) *ᵥ t) = A *ᵥ v + b := by
    intro v
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul T hT, Matrix.mul_one]
    abel
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp only [ellipsoidBody, Set.mem_setOf_eq, hkey v]
    exact hv
  · intro hw
    have hback : T *ᵥ (T⁻¹ *ᵥ (w - t)) + t = w := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hT, Matrix.one_mulVec]
      abel
    refine ⟨T⁻¹ *ᵥ (w - t), ?_, hback⟩
    simp only [ellipsoidBody, Set.mem_setOf_eq, ← hkey (T⁻¹ *ᵥ (w - t)), hback]
    exact hw

end LJAux

open ConvexOptimization in
theorem solution {nn : ℕ}
    (T : Matrix (Fin nn) (Fin nn) ℝ) (hT : IsUnit T.det) (t : Fin nn → ℝ)
    (S : Set (Fin nn → ℝ)) (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ)
    (h : IsLownerJohn A b S) :
    ∃ (A' : Matrix (Fin nn) (Fin nn) ℝ) (b' : Fin nn → ℝ),
      IsLownerJohn A' b' ((fun v => T.mulVec v + t) '' S) ∧
      ellipsoidBody A' b' = (fun v => T.mulVec v + t) '' ellipsoidBody A b := by
  classical
  obtain ⟨hAsymm, hApd, hScov, hAmin⟩ := h
  have hTne : T.det ≠ 0 := hT.ne_zero
  have hAdetpos : 0 < A.det := hApd.det_pos
  -- `M = A T⁻¹` represents the image ellipsoid; symmetrize it.
  set M : Matrix (Fin nn) (Fin nn) ℝ := A * T⁻¹ with hMdef
  have hMT : M * T = A := by
    rw [hMdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul T hT, Matrix.mul_one]
  have hMdet : M.det * T.det = A.det := by rw [← Matrix.det_mul, hMT]
  have hMunit : IsUnit M.det := by
    refine isUnit_iff_ne_zero.mpr fun hcon => ?_
    rw [hcon, zero_mul] at hMdet
    exact hAdetpos.ne hMdet
  obtain ⟨A', b', hA'symm, hA'pd, hA'det, hA'eq⟩ :=
    LJAux.exists_symm_repr M hMunit (b - M *ᵥ t)
  have himg : ellipsoidBody A' b' = (fun v => T *ᵥ v + t) '' ellipsoidBody A b := by
    rw [hA'eq, LJAux.image_ellipsoidBody T A hT t b]
  refine ⟨A', b', ⟨hA'symm, hA'pd, ?_, ?_⟩, himg⟩
  · -- The image of the covering ellipsoid covers the image of `S`.
    rw [himg]
    exact Set.image_mono hScov
  · -- Minimality transfers by pulling competitors back through the affine map.
    intro A₂ b₂ hA₂symm hA₂pd hA₂cov
    have hA₂detpos : 0 < A₂.det := hA₂pd.det_pos
    -- Pull back: `S ⊆ {v | ‖A₂ T v + (A₂ t + b₂)‖ ≤ 1}`.
    have hpull : S ⊆ ellipsoidBody (A₂ * T) (A₂ *ᵥ t + b₂) := by
      intro v hv
      have hmem : (fun v => T *ᵥ v + t) v ∈ ellipsoidBody A₂ b₂ :=
        hA₂cov ⟨v, hv, rfl⟩
      have hrw : A₂ *ᵥ (T *ᵥ v + t) + b₂ = (A₂ * T) *ᵥ v + (A₂ *ᵥ t + b₂) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
        abel
      simp only [ellipsoidBody, Set.mem_setOf_eq, hrw] at hmem
      exact hmem
    have hA₂Tunit : IsUnit (A₂ * T).det := by
      rw [Matrix.det_mul]
      exact isUnit_iff_ne_zero.mpr (mul_ne_zero hA₂detpos.ne' hTne)
    obtain ⟨A₃, b₃, hA₃symm, hA₃pd, hA₃det, hA₃eq⟩ :=
      LJAux.exists_symm_repr (A₂ * T) hA₂Tunit (A₂ *ᵥ t + b₂)
    have hcov₃ : S ⊆ ellipsoidBody A₃ b₃ := by rw [hA₃eq]; exact hpull
    have hle := hAmin A₃ b₃ hA₃symm hA₃pd hcov₃
    rw [hA₃det, Matrix.det_mul, abs_mul, abs_of_pos hA₂detpos] at hle
    -- `det A₂ * |det T| ≤ det A = |det M| * |det T|`
    have hAabs : A.det = |M.det| * |T.det| := by
      rw [← abs_mul, hMdet, abs_of_pos hAdetpos]
    rw [hAabs] at hle
    have hTabs : 0 < |T.det| := abs_pos.mpr hTne
    rw [hA'det]
    exact le_of_mul_le_mul_right hle hTabs
