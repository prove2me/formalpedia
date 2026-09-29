-- Prove2me | solution 1 for ShorIrreducible.frobInner_truncation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:41:18.747854+00:00
-- url     : https://prove2.me/submissions/ec6f222a-2cec-4851-9f2c-cc62c3808e49

import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorTruncationBound

set_option maxHeartbeats 2000000 in
open Finset Matrix IITTensorNetwork ShorIrreducible in
theorem solution {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq γ] [DecidableEq δ]
    {M : Matrix α β ℂ} {L : Matrix α γ ℂ} {R : Matrix β γ ℂ}
    {w : γ → ℝ} {s : δ → ℝ} (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (e : δ ↪ γ)
    (hM : M = L * Matrix.diagonal (fun j => (w j : ℂ)) * Rᴴ) :
    frobInner M ((L.submatrix id e) * Matrix.diagonal (fun k => (s k : ℂ))
        * (R.submatrix id e)ᴴ)
      = ∑ k, (w (e k) : ℂ) * (s k : ℂ) := by
  classical
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
  subst hM
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
