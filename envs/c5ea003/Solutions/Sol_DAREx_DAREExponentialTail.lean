-- Prove2me | solution 1 for DAREx.DAREExponentialTail
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-29T22:01:17.657766+00:00
-- url     : https://prove2.me/submissions/905dd122-dc0e-4f71-8beb-2b89cb191db7

import Definitions.Def_DAREx_Model
import Theorems.Thm_DAREx_KearnsSaulMGF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators
open DAREx

private lemma finite_chernoff {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (f : Mask n → ℝ) (t s : ℝ) (hs : 0 ≤ s) :
    probability p (fun ω ↦ t < f ω) ≤
      Real.exp (-s * t) * mean p (fun ω ↦ Real.exp (s * f ω)) := by
  classical
  unfold probability mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  have hw := maskMass_nonneg hp hp' ω
  by_cases he : t < f ω
  · rw [if_pos he]
    have hexp : 1 ≤ Real.exp (-s * t) * Real.exp (s * f ω) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.2
      have h := mul_le_mul_of_nonneg_left he.le hs
      linarith
    calc
      maskMass p ω = maskMass p ω * 1 := by ring
      _ ≤ maskMass p ω * (Real.exp (-s * t) * Real.exp (s * f ω)) :=
        mul_le_mul_of_nonneg_left hexp hw
      _ = Real.exp (-s * t) * (maskMass p ω * Real.exp (s * f ω)) := by ring
  · rw [if_neg he]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hw (Real.exp_pos _).le)

private lemma finite_absolute_union {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (f : Mask n → ℝ) (t : ℝ) :
    probability p (fun ω ↦ t < |f ω|) ≤
      probability p (fun ω ↦ t < f ω) + probability p (fun ω ↦ t < -f ω) := by
  classical
  unfold probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have hw := maskMass_nonneg hp hp' ω
  by_cases hbad : t < |f ω|
  · rw [if_pos hbad]
    rcases lt_abs.1 hbad with hpos | hneg
    · rw [if_pos hpos]
      split_ifs <;> linarith
    · have hneg' : t < -f ω := by linarith
      rw [if_pos hneg']
      split_ifs <;> linarith
  · rw [if_neg hbad]
    split_ifs <;> linarith

private lemma finite_subgaussian_absolute_tail {n : ℕ} (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (f : Mask n → ℝ) (a t : ℝ)
    (ha : 0 < a) (ht : 0 < t)
    (hmgf : ∀ s : ℝ, mean p (fun ω ↦ Real.exp (s * f ω)) ≤
      Real.exp (a * s ^ 2)) :
    probability p (fun ω ↦ t < |f ω|) ≤ 2 * Real.exp (-(t ^ 2 / (4 * a))) := by
  let s := t / (2 * a)
  have hs : 0 < s := div_pos ht (mul_pos (by norm_num) ha)
  have hright : probability p (fun ω ↦ t < f ω) ≤
      Real.exp (-s * t) * Real.exp (a * s ^ 2) :=
    (finite_chernoff p hp hp' f t s hs.le).trans
      (mul_le_mul_of_nonneg_left (hmgf s) (Real.exp_pos _).le)
  have hleftmgf : mean p (fun ω ↦ Real.exp (s * -f ω)) ≤
      Real.exp (a * s ^ 2) := by
    simpa only [mul_neg, neg_mul, neg_sq] using hmgf (-s)
  have hleft : probability p (fun ω ↦ t < -f ω) ≤
      Real.exp (-s * t) * Real.exp (a * s ^ 2) :=
    (finite_chernoff p hp hp' (fun ω ↦ -f ω) t s hs.le).trans
      (mul_le_mul_of_nonneg_left hleftmgf (Real.exp_pos _).le)
  have hopt : -s * t + a * s ^ 2 = -(t ^ 2 / (4 * a)) := by
    dsimp [s]
    field_simp
    ring
  have hsum := (finite_absolute_union p hp hp' f t).trans (add_le_add hright hleft)
  rw [← Real.exp_add, hopt] at hsum
  linarith

private lemma factorized_mgf {n : ℕ} (p : ℝ) (a : Fin n → Bool → ℝ) :
    mean p (fun ω ↦ Real.exp (∑ j, a j (ω j))) =
      ∏ j, ((1 - p) * Real.exp (a j false) + p * Real.exp (a j true)) := by
  unfold mean maskMass
  simp_rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  simpa [add_comm] using (Fintype.prod_sum (fun (j : Fin n) (b : Bool) ↦
    (if b then p else 1 - p) * Real.exp (a j b))).symm

private lemma scaled_dareError {n : ℕ} (p s : ℝ) (c : Fin n → ℝ) (hp : p < 1)
    (ω : Mask n) :
    s * dareError p c ω =
      ∑ j, (s * c j / (1 - p)) * ((if ω j then (1 : ℝ) else 0) - p) := by
  have hq : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  unfold dareError outputError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases hb : ω j <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · field_simp
    ring
  · field_simp
    ring

private lemma dare_mgf_bound {n : ℕ} (p s : ℝ) (c : Fin n → ℝ)
    (hp : 0 < p) (hp' : p < 1)
    (hks : ∀ u : ℝ,
      (1 - p) * Real.exp (-u * p) + p * Real.exp (u * (1 - p)) ≤
        Real.exp (phi p * u ^ 2 / 4)) :
    mean p (fun ω ↦ Real.exp (s * dareError p c ω)) ≤
      Real.exp (phi p * energy c * s ^ 2 / (4 * (1 - p) ^ 2)) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp'
  have hq' : 1 - p ≠ 0 := ne_of_gt hq
  simp_rw [scaled_dareError p s c hp']
  rw [factorized_mgf p
    (fun j b ↦ (s * c j / (1 - p)) * ((if b then (1 : ℝ) else 0) - p))]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_sub, mul_neg]
  calc
    _ ≤ ∏ j, Real.exp (phi p * (s * c j / (1 - p)) ^ 2 / 4) := by
      apply Finset.prod_le_prod
      · intro j _
        exact add_nonneg (mul_nonneg hq.le (Real.exp_pos _).le)
          (mul_nonneg hp.le (Real.exp_pos _).le)
      · intro j _
        simpa only [neg_mul] using hks (s * c j / (1 - p))
    _ = Real.exp (∑ j, phi p * (s * c j / (1 - p)) ^ 2 / 4) :=
      (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      have hterm (j : Fin n) :
          phi p * (s * c j / (1 - p)) ^ 2 / 4 =
            (phi p * s ^ 2 / (4 * (1 - p) ^ 2)) * c j ^ 2 := by
        field_simp
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      unfold energy
      ring

private lemma dare_tail_from_scalar {n : ℕ} (c : Fin n → ℝ) (p t : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hQ : 0 < energy c) (ht : 0 < t)
    (hphi : 0 < phi p)
    (hks : ∀ u : ℝ,
      (1 - p) * Real.exp (-u * p) + p * Real.exp (u * (1 - p)) ≤
        Real.exp (phi p * u ^ 2 / 4)) :
    probability p (fun ω ↦ t < |dareError p c ω|) ≤
      2 * Real.exp (-(t ^ 2 * (1 - p) ^ 2 / (phi p * energy c))) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp'
  let a := phi p * energy c / (4 * (1 - p) ^ 2)
  have ha : 0 < a := div_pos (mul_pos hphi hQ)
    (mul_pos (by norm_num) (sq_pos_of_pos hq))
  have hmgf (s : ℝ) : mean p (fun ω ↦ Real.exp (s * dareError p c ω)) ≤
      Real.exp (a * s ^ 2) := by
    convert dare_mgf_bound p s c hp hp' hks using 1
    dsimp [a]
    congr 1
    ring
  have h := finite_subgaussian_absolute_tail p hp.le hp'.le (dareError p c) a t ha ht hmgf
  have hid : t ^ 2 / (4 * a) = t ^ 2 * (1 - p) ^ 2 / (phi p * energy c) := by
    dsimp [a]
    field_simp
  rw [hid] at h
  exact h

-- Deng et al., Appendix E.1, PDF p. 30, tail display preceding equation (8).
-- All finite-product and Chernoff steps are proved; only the scalar MGF is assumed.
theorem solution :
    ∀ (n : ℕ) (c : Fin n → ℝ) (p t : ℝ),
      0 < p → p < 1 → 0 < energy c → 0 < t →
      probability p (fun ω ↦ t < |dareError p c ω|) ≤
        2 * Real.exp (-(t ^ 2 * (1 - p) ^ 2 / (phi p * energy c))) := by
  intro n c p t hp hp' hQ ht
  have hks := KearnsSaulMGF p hp hp'
  exact dare_tail_from_scalar c p t hp hp' hQ ht hks.1 hks.2.2
