-- Prove2me | solution 1 for ShorIrreducible.frobInner_schmidtForms
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:41:17.843761+00:00
-- url     : https://prove2.me/submissions/53e92270-58f2-4223-a4d9-4ed8bb1861ac

import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorTruncationBound

set_option maxHeartbeats 2000000 in
open Finset Matrix IITTensorNetwork ShorIrreducible in
theorem solution {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq γ] [DecidableEq δ]
    {M A : Matrix α β ℂ} {L : Matrix α γ ℂ} {R : Matrix β γ ℂ}
    {P : Matrix α δ ℂ} {Q : Matrix β δ ℂ} {w : γ → ℝ} {s : δ → ℝ}
    (hM : M = L * Matrix.diagonal (fun j => (w j : ℂ)) * Rᴴ)
    (hA : A = P * Matrix.diagonal (fun k => (s k : ℂ)) * Qᴴ) :
    frobInner M A
      = ∑ k, (∑ j, (Qᴴ * R) k j * (w j : ℂ) * (Lᴴ * P) j k) * (s k : ℂ) := by
  classical
  have hD : (Matrix.diagonal (fun j => (w j : ℂ)))ᴴ = Matrix.diagonal (fun j => (w j : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    simp [Complex.conj_ofReal]
  subst hM
  subst hA
  rw [frobInner, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hD]
  -- cycle `Qᴴ` to the front of the trace
  have h1 : (R * ((Matrix.diagonal (fun j => (w j : ℂ))) * Lᴴ))
        * ((P * Matrix.diagonal (fun k => (s k : ℂ))) * Qᴴ)
      = (R * Matrix.diagonal (fun j => (w j : ℂ)) * Lᴴ * P
          * Matrix.diagonal (fun k => (s k : ℂ))) * Qᴴ := by
    simp [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : Qᴴ * (R * Matrix.diagonal (fun j => (w j : ℂ)) * Lᴴ * P
        * Matrix.diagonal (fun k => (s k : ℂ)))
      = ((Qᴴ * R) * Matrix.diagonal (fun j => (w j : ℂ)) * (Lᴴ * P))
          * Matrix.diagonal (fun k => (s k : ℂ)) := by
    simp [Matrix.mul_assoc]
  rw [h2]
  -- read off the diagonal: both diagonals collapse their sums
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
