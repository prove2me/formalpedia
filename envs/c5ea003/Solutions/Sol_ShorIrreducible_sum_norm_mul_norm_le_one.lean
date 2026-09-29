-- Prove2me | solution 1 for ShorIrreducible.sum_norm_mul_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:41:17.961657+00:00
-- url     : https://prove2.me/submissions/8cb36df2-4805-4f1b-8295-a1c5a3b00560

import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorTruncationBound

set_option maxHeartbeats 2000000 in
open Finset Matrix IITTensorNetwork ShorIrreducible in
theorem solution {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {L : Matrix α γ ℂ} {R : Matrix β γ ℂ} {P : Matrix α δ ℂ} {Q : Matrix β δ ℂ}
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1) (k : δ) :
    ∑ j, ‖(Qᴴ * R) k j‖ * ‖(Lᴴ * P) j k‖ ≤ 1 := by
  classical
  have bess1 : ∑ j, ‖(Qᴴ * R) k j‖ ^ 2 ≤ 1 := by
    set N1 : Matrix β β ℂ := 1 - R * Rᴴ with hN1
    have hRRN1 : R * Rᴴ * (R * Rᴴ) = R * Rᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ R Rᴴ, hR, Matrix.one_mul]
    have hhermN1 : N1ᴴ = N1 := by
      rw [hN1, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have hidemN1 : N1 * N1 = N1 := by
      rw [hN1, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hRRN1]
      abel
    have hkeyN1 : (N1 * Q)ᴴ * (N1 * Q) = 1 - (Qᴴ * R) * (Qᴴ * R)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc N1ᴴ N1 Q,
        hhermN1, hidemN1, hN1, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hQ]
      all_goals
        congr 1
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        simp [Matrix.mul_assoc]
    have hLN1 : ((N1 * Q)ᴴ * (N1 * Q)) k k
        = ((∑ b, ‖(N1 * Q) b k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.mul_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj]
      all_goals simp [Complex.normSq_eq_norm_sq]
    have hRN1 : ((Qᴴ * R) * (Qᴴ * R)ᴴ) k k
        = ((∑ j, ‖(Qᴴ * R) k j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.mul_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]
      all_goals simp [Complex.normSq_eq_norm_sq]
    have hEqN1 : ((∑ b, ‖(N1 * Q) b k‖ ^ 2 : ℝ) : ℂ)
        = 1 - ((∑ j, ‖(Qᴴ * R) k j‖ ^ 2 : ℝ) : ℂ) := by
      rw [← hLN1, hkeyN1, Matrix.sub_apply, Matrix.one_apply_eq, hRN1]
    have hnnN1 : (0 : ℝ) ≤ ∑ b, ‖(N1 * Q) b k‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hrealN1 : (∑ b, ‖(N1 * Q) b k‖ ^ 2 : ℝ)
        = 1 - (∑ j, ‖(Qᴴ * R) k j‖ ^ 2 : ℝ) := by exact_mod_cast hEqN1
    linarith [hnnN1, hrealN1.le, hrealN1.symm.le]
  have bess2 : ∑ j, ‖(Pᴴ * L) k j‖ ^ 2 ≤ 1 := by
    set N2 : Matrix α α ℂ := 1 - L * Lᴴ with hN2
    have hRRN2 : L * Lᴴ * (L * Lᴴ) = L * Lᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ L Lᴴ, hL, Matrix.one_mul]
    have hhermN2 : N2ᴴ = N2 := by
      rw [hN2, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have hidemN2 : N2 * N2 = N2 := by
      rw [hN2, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hRRN2]
      abel
    have hkeyN2 : (N2 * P)ᴴ * (N2 * P) = 1 - (Pᴴ * L) * (Pᴴ * L)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc N2ᴴ N2 P,
        hhermN2, hidemN2, hN2, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hP]
      all_goals
        congr 1
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        simp [Matrix.mul_assoc]
    have hLN2 : ((N2 * P)ᴴ * (N2 * P)) k k
        = ((∑ b, ‖(N2 * P) b k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.mul_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj]
      all_goals simp [Complex.normSq_eq_norm_sq]
    have hRN2 : ((Pᴴ * L) * (Pᴴ * L)ᴴ) k k
        = ((∑ j, ‖(Pᴴ * L) k j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.mul_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]
      all_goals simp [Complex.normSq_eq_norm_sq]
    have hEqN2 : ((∑ b, ‖(N2 * P) b k‖ ^ 2 : ℝ) : ℂ)
        = 1 - ((∑ j, ‖(Pᴴ * L) k j‖ ^ 2 : ℝ) : ℂ) := by
      rw [← hLN2, hkeyN2, Matrix.sub_apply, Matrix.one_apply_eq, hRN2]
    have hnnN2 : (0 : ℝ) ≤ ∑ b, ‖(N2 * P) b k‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hrealN2 : (∑ b, ‖(N2 * P) b k‖ ^ 2 : ℝ)
        = 1 - (∑ j, ‖(Pᴴ * L) k j‖ ^ 2 : ℝ) := by exact_mod_cast hEqN2
    linarith [hnnN2, hrealN2.le, hrealN2.symm.le]
  -- the second factor is the conjugate of an entry of `Pᴴ L`
  have hconv : ∀ j, ‖(Lᴴ * P) j k‖ = ‖(Pᴴ * L) k j‖ := by
    intro j
    have hct : (Pᴴ * L)ᴴ = Lᴴ * P := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have h : (Lᴴ * P) j k = star ((Pᴴ * L) k j) := by
      rw [← hct, Matrix.conjTranspose_apply]
    rw [h, norm_star]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hconv j])]
  -- Cauchy-Schwarz against the two Bessel bounds
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset γ)
    (fun j => ‖(Qᴴ * R) k j‖) (fun j => ‖(Pᴴ * L) k j‖)
  have hpos : (0 : ℝ) ≤ ∑ j, ‖(Qᴴ * R) k j‖ * ‖(Pᴴ * L) k j‖ :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hA : (0 : ℝ) ≤ ∑ j, ‖(Qᴴ * R) k j‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hB : (0 : ℝ) ≤ ∑ j, ‖(Pᴴ * L) k j‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hprod : (∑ j, ‖(Qᴴ * R) k j‖ ^ 2) * (∑ j, ‖(Pᴴ * L) k j‖ ^ 2) ≤ 1 := by
    first
      | exact mul_le_one₀ bess1 hB bess2
      | exact mul_le_one bess1 hB bess2
      | nlinarith [bess1, bess2, hA, hB]
  nlinarith [hcs, hprod, hpos]
