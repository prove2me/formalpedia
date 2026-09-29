-- Prove2me | solution 1 for ShorIrreducible.norm_frobInner_flat_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:59:22.248017+00:00
-- url     : https://prove2.me/submissions/c04f8df0-9742-49c7-a4d5-2031b6da0058

import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorTruncationBound

set_option maxHeartbeats 4000000 in
open Finset Matrix IITTensorNetwork ShorIrreducible in
theorem solution {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {M A : Matrix α β ℂ} {L : Matrix α γ ℂ} {R : Matrix β γ ℂ}
    {P : Matrix α δ ℂ} {Q : Matrix β δ ℂ} {w : γ → ℝ} {s : δ → ℝ}
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1)
    (hM : M = L * Matrix.diagonal (fun j => (w j : ℂ)) * Rᴴ)
    (hA : A = P * Matrix.diagonal (fun k => (s k : ℂ)) * Qᴴ)
    (hw : ∀ j, |w j| ≤ (Real.sqrt (Fintype.card γ))⁻¹) (hs : ∑ k, s k ^ 2 ≤ 1) :
    ‖frobInner M A‖ ≤ Real.sqrt ((Fintype.card δ : ℝ) / (Fintype.card γ : ℝ)) := by
  classical
  -- (1) the Schmidt-form expansion of the inner product
  have hexp : frobInner M A
      = ∑ k, (∑ j, (Qᴴ * R) k j * (w j : ℂ) * (Lᴴ * P) j k) * (s k : ℂ) := by
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
  -- (2) the overlap bound, for each fixed `k`
  have hov : ∀ k : δ, ∑ j, ‖(Qᴴ * R) k j‖ * ‖(Lᴴ * P) j k‖ ≤ 1 := by
    intro k
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
  -- (3) each inner sum is at most `(√|γ|)⁻¹`
  have hGnn : (0 : ℝ) ≤ (Real.sqrt (Fintype.card γ))⁻¹ := by positivity
  have hterm : ∀ k : δ, ‖∑ j, (Qᴴ * R) k j * (w j : ℂ) * (Lᴴ * P) j k‖
      ≤ (Real.sqrt (Fintype.card γ))⁻¹ := by
    intro k
    refine le_trans (norm_sum_le _ _) ?_
    have hle : ∀ j ∈ (Finset.univ : Finset γ),
        ‖(Qᴴ * R) k j * (w j : ℂ) * (Lᴴ * P) j k‖
          ≤ (Real.sqrt (Fintype.card γ))⁻¹ * (‖(Qᴴ * R) k j‖ * ‖(Lᴴ * P) j k‖) := by
      intro j _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖(Qᴴ * R) k j‖ * |w j| * ‖(Lᴴ * P) j k‖
          = (‖(Qᴴ * R) k j‖ * ‖(Lᴴ * P) j k‖) * |w j| := by ring
        _ ≤ (‖(Qᴴ * R) k j‖ * ‖(Lᴴ * P) j k‖) * (Real.sqrt (Fintype.card γ))⁻¹ :=
            mul_le_mul_of_nonneg_left (hw j) (by positivity)
        _ = (Real.sqrt (Fintype.card γ))⁻¹ * (‖(Qᴴ * R) k j‖ * ‖(Lᴴ * P) j k‖) := by ring
    refine le_trans (Finset.sum_le_sum hle) ?_
    rw [← Finset.mul_sum]
    calc (Real.sqrt (Fintype.card γ))⁻¹ * ∑ j, ‖(Qᴴ * R) k j‖ * ‖(Lᴴ * P) j k‖
        ≤ (Real.sqrt (Fintype.card γ))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hov k) hGnn
      _ = (Real.sqrt (Fintype.card γ))⁻¹ := mul_one _
  -- (4) sum over `k`, then Cauchy-Schwarz on `∑ |s k|`
  have habs : ∑ k, |s k| ≤ Real.sqrt (Fintype.card δ) := by
    have hnn : (0 : ℝ) ≤ ∑ k, |s k| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hcs : (∑ k, |s k|) ^ 2
        ≤ ((Finset.univ : Finset δ).card : ℝ) * ∑ k, |s k| ^ 2 := by
      first
        | exact sq_sum_le_card_mul_sum_sq
        | exact Finset.sq_sum_le_card_mul_sum_sq
    have hsq : ∑ k, |s k| ^ 2 = ∑ k, s k ^ 2 :=
      Finset.sum_congr rfl (fun k _ => sq_abs (s k))
    rw [hsq, Finset.card_univ] at hcs
    have hcard : (0 : ℝ) ≤ (Fintype.card δ : ℝ) := by positivity
    have hb : (∑ k, |s k|) ^ 2 ≤ (Fintype.card δ : ℝ) := by nlinarith [hcs, hs, hcard]
    calc ∑ k, |s k| = Real.sqrt ((∑ k, |s k|) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (Fintype.card δ) := Real.sqrt_le_sqrt hb
  rw [hexp]
  refine le_trans (norm_sum_le _ _) ?_
  have hstep : ∀ k ∈ (Finset.univ : Finset δ),
      ‖(∑ j, (Qᴴ * R) k j * (w j : ℂ) * (Lᴴ * P) j k) * (s k : ℂ)‖
        ≤ (Real.sqrt (Fintype.card γ))⁻¹ * |s k| := by
    intro k _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hterm k) (abs_nonneg _)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hGpos : (0 : ℝ) ≤ Real.sqrt (Fintype.card γ) := Real.sqrt_nonneg _
  calc (Real.sqrt (Fintype.card γ))⁻¹ * ∑ k, |s k|
      ≤ (Real.sqrt (Fintype.card γ))⁻¹ * Real.sqrt (Fintype.card δ) :=
        mul_le_mul_of_nonneg_left habs hGnn
    _ = Real.sqrt ((Fintype.card δ : ℝ) / (Fintype.card γ : ℝ)) := by
        rw [show ((Fintype.card δ : ℝ) / (Fintype.card γ : ℝ))
            = (Fintype.card δ : ℝ) * ((Fintype.card γ : ℝ))⁻¹ from by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_inv]
        ring
