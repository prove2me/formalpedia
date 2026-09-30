-- Prove2me | solution 1 for DAREx.RescaledErrorMoments
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-29T22:50:57.214244+00:00
-- url     : https://prove2.me/submissions/2b078813-c9cb-4a09-9230-afe8653a792a

import Definitions.Def_DAREx_Model
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators
open DAREx

-- Fin.consEquiv and the finite product/sum APIs supply the independence calculation.
private lemma mean_cons {n : ℕ} (p : ℝ) (f : Mask (n + 1) → ℝ) :
    mean p f = (1 - p) * mean p (fun ω ↦ f (Fin.cons false ω)) +
      p * mean p (fun ω ↦ f (Fin.cons true ω)) := by
  unfold mean
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)).sum_comp
    (fun ω ↦ maskMass p ω * f ω)]
  rw [Fintype.sum_prod_type]
  simp [maskMass, Fin.prod_univ_succ, Finset.mul_sum, mul_assoc]
  exact add_comm _ _

private lemma mean_const {n : ℕ} (p a : ℝ) :
    mean p (fun _ : Mask n ↦ a) = a := by
  unfold mean
  rw [← Finset.sum_mul, maskMass_sum, one_mul]

private lemma mean_add {n : ℕ} (p : ℝ) (f g : Mask n → ℝ) :
    mean p (fun ω ↦ f ω + g ω) = mean p f + mean p g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

private lemma mean_mul {n : ℕ} (p a : ℝ) (f : Mask n → ℝ) :
    mean p (fun ω ↦ a * f ω) = a * mean p f := by
  simp [mean, Finset.mul_sum, mul_left_comm]

private lemma mean_shift_sq {n : ℕ} (p a : ℝ) (f : Mask n → ℝ) :
    mean p (fun ω ↦ (a + f ω) ^ 2) =
      a ^ 2 + 2 * a * mean p f + mean p (fun ω ↦ f ω ^ 2) := by
  have h : (fun ω ↦ (a + f ω) ^ 2) =
      (fun ω ↦ (a ^ 2 + (2 * a) * f ω) + f ω ^ 2) := by
    funext ω
    ring
  rw [h, mean_add, mean_add, mean_const, mean_mul]

private lemma error_cons {n : ℕ} (q : ℝ) (c : Fin (n + 1) → ℝ)
    (b : Bool) (ω : Mask n) :
    outputError q c (Fin.cons b ω) =
      (c 0 - (if b then 0 else c 0 / q)) + outputError q (fun j ↦ c j.succ) ω := by
  simp [outputError, Fin.sum_univ_succ]
  ring

private lemma bias_cons {n : ℕ} (p q : ℝ) (c : Fin (n + 1) → ℝ) :
    outputBias p q c = (1 - (1 - p) / q) * c 0 +
      outputBias p q (fun j ↦ c j.succ) := by
  simp [outputBias, coefficientSum, Fin.sum_univ_succ, mul_add]

private lemma energy_cons {n : ℕ} (c : Fin (n + 1) → ℝ) :
    energy c = c 0 ^ 2 + energy (fun j ↦ c j.succ) := by
  simp [energy, Fin.sum_univ_succ]

private lemma raw_moments (n : ℕ) (c : Fin n → ℝ) (p q : ℝ) (hq : 0 < q) :
    mean p (outputError q c) = outputBias p q c ∧
    mean p (fun ω ↦ outputError q c ω ^ 2) =
      outputBias p q c ^ 2 + p * (1 - p) / q ^ 2 * energy c := by
  induction n with
  | zero => simp [outputError, outputBias, coefficientSum, energy, mean]
  | succ n ih =>
    obtain ⟨hfirst, hsecond⟩ := ih (fun j ↦ c j.succ)
    constructor
    · rw [mean_cons, bias_cons]
      simp_rw [error_cons]
      simp only [Bool.false_eq_true, if_false, if_true, sub_zero]
      rw [mean_add, mean_add, mean_const, mean_const, hfirst]
      field_simp
      ring
    · rw [mean_cons, bias_cons, energy_cons]
      simp_rw [error_cons]
      simp only [Bool.false_eq_true, if_false, if_true, sub_zero]
      rw [mean_shift_sq, mean_shift_sq, hfirst, hsecond]
      field_simp
      ring

theorem solution :
    ∀ (n : ℕ) (c : Fin n → ℝ) (p q : ℝ), 0 ≤ p → p ≤ 1 → 0 < q →
      mean p (outputError q c) = outputBias p q c ∧
      mean p (fun ω ↦ (outputError q c ω - outputBias p q c) ^ 2) =
        p * (1 - p) / q ^ 2 * energy c ∧
      mean p (fun ω ↦ outputError q c ω ^ 2) =
        outputBias p q c ^ 2 + p * (1 - p) / q ^ 2 * energy c := by
  intro n c p q _hp _hp' hq
  obtain ⟨hfirst, hsecond⟩ := raw_moments n c p q hq
  refine ⟨hfirst, ?_, hsecond⟩
  have h : (fun ω ↦ (outputError q c ω - outputBias p q c) ^ 2) =
      (fun ω ↦ (-outputBias p q c + outputError q c ω) ^ 2) := by
    funext ω
    ring
  rw [h, mean_shift_sq, hfirst, hsecond]
  ring
