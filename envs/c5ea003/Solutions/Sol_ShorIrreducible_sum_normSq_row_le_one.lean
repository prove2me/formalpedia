-- Prove2me | solution 1 for ShorIrreducible.sum_normSq_row_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:38:04.718391+00:00
-- url     : https://prove2.me/submissions/a60269a8-5728-4efa-84be-946647f713c0

import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorTruncationBound

set_option maxHeartbeats 1000000 in
open Finset Matrix IITTensorNetwork ShorIrreducible in
theorem solution {β γ δ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    [DecidableEq δ]
    {R : Matrix β γ ℂ} {Q : Matrix β δ ℂ}
    (hR : Rᴴ * R = 1) (hQ : Qᴴ * Q = 1) (k : δ) :
    ∑ j, ‖(Qᴴ * R) k j‖ ^ 2 ≤ 1 := by
  classical
  -- `N = 1 - R Rᴴ` is the orthogonal projection onto the complement of the range of `R`
  set N : Matrix β β ℂ := 1 - R * Rᴴ with hN
  have hRR : R * Rᴴ * (R * Rᴴ) = R * Rᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ R Rᴴ, hR, Matrix.one_mul]
  have hNherm : Nᴴ = N := by
    rw [hN, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hNidem : N * N = N := by
    rw [hN, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hRR]
    abel
  -- `(N Q)ᴴ (N Q) = Qᴴ N Q = 1 - (Qᴴ R)(Qᴴ R)ᴴ`
  have hkey : (N * Q)ᴴ * (N * Q) = 1 - (Qᴴ * R) * (Qᴴ * R)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Nᴴ N Q, hNherm, hNidem,
      hN, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hQ]
    all_goals
      congr 1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp [Matrix.mul_assoc]
  -- read both sides of `hkey` at `(k,k)`
  have hL : ((N * Q)ᴴ * (N * Q)) k k = ((∑ b, ‖(N * Q) b k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj]
    all_goals simp [Complex.normSq_eq_norm_sq]
  have hRrow : ((Qᴴ * R) * (Qᴴ * R)ᴴ) k k = ((∑ j, ‖(Qᴴ * R) k j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]
    all_goals simp [Complex.normSq_eq_norm_sq]
  have hEq : ((∑ b, ‖(N * Q) b k‖ ^ 2 : ℝ) : ℂ)
      = 1 - ((∑ j, ‖(Qᴴ * R) k j‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hL, hkey, Matrix.sub_apply, Matrix.one_apply_eq, hRrow]
  -- the left-hand sum is a sum of squares, hence nonnegative
  have hnn : (0 : ℝ) ≤ ∑ b, ‖(N * Q) b k‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hreal : (∑ b, ‖(N * Q) b k‖ ^ 2 : ℝ)
      = 1 - (∑ j, ‖(Qᴴ * R) k j‖ ^ 2 : ℝ) := by exact_mod_cast hEq
  linarith [hnn, hreal.symm.le, hreal.le]
