-- Prove2me | solution 1 for ShorIrreducible.fidelity_flat_truncation_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T02:13:33.227033+00:00
-- url     : https://prove2.me/submissions/38e020ac-3ce4-4f20-a2e5-00da8a05a445

import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorTruncationBound

set_option maxHeartbeats 2000000 in
open Finset Matrix IITTensorNetwork ShorIrreducible in
theorem solution {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq γ] [DecidableEq δ]
    {M : Matrix α β ℂ} {L : Matrix α γ ℂ} {R : Matrix β γ ℂ}
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (e : δ ↪ γ) (hD : 0 < Fintype.card δ)
    (hM : M = L * Matrix.diagonal
      (fun _ : γ => (((Real.sqrt (Fintype.card γ))⁻¹ : ℝ) : ℂ)) * Rᴴ) :
    ‖frobInner M ((L.submatrix id e)
        * Matrix.diagonal (fun _ : δ => (((Real.sqrt (Fintype.card δ))⁻¹ : ℝ) : ℂ))
        * (R.submatrix id e)ᴴ)‖ ^ 2
      = (Fintype.card δ : ℝ) / (Fintype.card γ : ℝ) := by
  classical
  -- the truncation identity (same argument as `frobInner_truncation`), stated for general weights
  have key : ∀ (w : γ → ℝ) (s : δ → ℝ) (M' : Matrix α β ℂ),
      M' = L * Matrix.diagonal (fun j => (w j : ℂ)) * Rᴴ →
      frobInner M' ((L.submatrix id e) * Matrix.diagonal (fun k => (s k : ℂ))
          * (R.submatrix id e)ᴴ)
        = ∑ k, (w (e k) : ℂ) * (s k : ℂ) := by
    intro w s M' hM'
    -- a real diagonal is self-adjoint
    have hD : (Matrix.diagonal (fun j => (w j : ℂ)))ᴴ = Matrix.diagonal (fun j => (w j : ℂ)) := by
      rw [Matrix.diagonal_conjTranspose]
      congr 1
      funext j
      simp [Complex.star_def, Complex.conj_ofReal]
    have hMH : (L * Matrix.diagonal (fun j => (w j : ℂ)) * Rᴴ)ᴴ
        = R * Matrix.diagonal (fun j => (w j : ℂ)) * Lᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
    -- the two isometry contractions
    have hLe : Lᴴ * (L.submatrix id e) = (1 : Matrix γ γ ℂ).submatrix id e := by
      ext j k
      have h := congrFun (congrFun hL j) (e k)
      rw [Matrix.mul_apply] at h
      rw [Matrix.mul_apply, Matrix.submatrix_apply]
      simpa [Matrix.conjTranspose_apply, Matrix.submatrix_apply] using h
    have hRe : (R.submatrix id e)ᴴ * R = (1 : Matrix γ γ ℂ).submatrix e id := by
      ext k j
      have h := congrFun (congrFun hR (e k)) j
      rw [Matrix.mul_apply] at h
      rw [Matrix.mul_apply, Matrix.submatrix_apply]
      simpa [Matrix.conjTranspose_apply, Matrix.submatrix_apply] using h
    subst hM'
    rw [frobInner, hMH]
    -- regroup so that `Lᴴ * L_e` appears, then cycle `R_eᴴ` to the front
    rw [show (R * Matrix.diagonal (fun j => (w j : ℂ)) * Lᴴ) *
          ((L.submatrix id e) * Matrix.diagonal (fun k => (s k : ℂ)) * (R.submatrix id e)ᴴ)
        = (R * Matrix.diagonal (fun j => (w j : ℂ)) * (Lᴴ * (L.submatrix id e))
            * Matrix.diagonal (fun k => (s k : ℂ))) * (R.submatrix id e)ᴴ from by
      simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm, hLe]
    rw [show (R.submatrix id e)ᴴ * (R * Matrix.diagonal (fun j => (w j : ℂ))
          * ((1 : Matrix γ γ ℂ).submatrix id e) * Matrix.diagonal (fun k => (s k : ℂ)))
        = ((R.submatrix id e)ᴴ * R) * Matrix.diagonal (fun j => (w j : ℂ))
            * ((1 : Matrix γ γ ℂ).submatrix id e) * Matrix.diagonal (fun k => (s k : ℂ)) from by
      simp [Matrix.mul_assoc]]
    rw [hRe]
    -- everything left is a selection, so the trace collapses to the diagonal
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.submatrix_apply,
      Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', e.injective.eq_iff]
  -- positivity of the two cardinalities
  have hDpos : (0 : ℝ) < (Fintype.card δ : ℝ) := by exact_mod_cast hD
  have hGpos : (0 : ℝ) < (Fintype.card γ : ℝ) := by
    have : Fintype.card δ ≤ Fintype.card γ := Fintype.card_le_of_embedding e
    exact_mod_cast lt_of_lt_of_le hD this
  have hsG : (0 : ℝ) < Real.sqrt (Fintype.card γ) := Real.sqrt_pos.mpr hGpos
  have hsD : (0 : ℝ) < Real.sqrt (Fintype.card δ) := Real.sqrt_pos.mpr hDpos
  rw [key (fun _ => (Real.sqrt (Fintype.card γ))⁻¹)
      (fun _ => (Real.sqrt (Fintype.card δ))⁻¹) M hM]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show ((Fintype.card δ : ℂ) * ((((Real.sqrt (Fintype.card γ))⁻¹ : ℝ) : ℂ)
        * (((Real.sqrt (Fintype.card δ))⁻¹ : ℝ) : ℂ)))
      = ((((Fintype.card δ : ℝ) * (Real.sqrt (Fintype.card γ))⁻¹
          * (Real.sqrt (Fintype.card δ))⁻¹ : ℝ)) : ℂ) from by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hGpos.le, Real.sq_sqrt hDpos.le]
  field_simp
