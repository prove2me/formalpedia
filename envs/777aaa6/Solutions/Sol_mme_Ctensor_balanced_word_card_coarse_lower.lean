-- Prove2me | solution 1 for mme_Ctensor_balanced_word_card_coarse_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:36:10.909301+00:00
-- url     : https://prove2.me/submissions/fd4777b7-00e7-459a-ba09-6c81ae7f57bc

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_mme_Ctensor_balanced_word_card

open BigOperators

set_option autoImplicit false

private theorem factorial_upper_coarse_balanced (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤
      6 * ((n + 1 : ℕ) : ℝ) * (((n : ℕ) : ℝ) / Real.exp 1) ^ n := by
  let k := n - 1
  have hnk : n = k + 1 := by
    dsimp [k]
    omega
  rw [hnk]
  have hs : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 := by
    simpa [Function.comp_apply] using
      (Stirling.stirlingSeq'_antitone (Nat.zero_le k))
  have hs3 : Stirling.stirlingSeq (k + 1) ≤ 3 := by
    refine hs.trans ?_
    rw [Stirling.stirlingSeq_one]
    refine (_root_.div_le_self (Real.exp_pos 1).le ?_).trans
      Real.exp_one_lt_three.le
    rw [Real.one_le_sqrt]
    norm_num
  have hden :
      0 < Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
        (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
    positivity
  rw [Stirling.stirlingSeq] at hs3
  have hfac :
      (((k + 1).factorial : ℕ) : ℝ) ≤
        3 * (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) :=
    (div_le_iff₀ hden).mp hs3
  have hsqrt :
      Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) ≤
        2 * (((k + 1 + 1 : ℕ) : ℝ)) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · push_cast
      nlinarith [sq_nonneg (k : ℝ)]
  have hp : 0 ≤ (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
    positivity
  calc
    (((k + 1).factorial : ℕ) : ℝ)
        ≤ 3 * (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) := hfac
    _ ≤ 3 * ((2 * (((k + 1 + 1 : ℕ) : ℝ))) *
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) := by
      gcongr
    _ = 6 * (((k + 1 + 1 : ℕ) : ℝ)) *
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by ring

private theorem factorial_lower_coarse_balanced (n : ℕ) (hn : 1 ≤ n) :
    (((n : ℕ) : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  apply le_trans ?_ (Stirling.le_factorial_stirling n)
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  have hp : 0 ≤ (((n : ℕ) : ℝ) / Real.exp 1) ^ n := by positivity
  exact le_mul_of_one_le_left hp hsqrt

theorem solution
    (H m : ℕ) (hH : 0 < H) (hm : 0 < m) :
    (H : ℝ) ^ (H * m) ≤
      (6 * (((m + 1 : ℕ) : ℝ))) ^ H *
        (Nat.card
          {w : Fin (H * m) → Fin H // ∀ h,
            Fintype.card {j // w j = h} = m} : ℝ) := by
  let R : ℕ := H * m
  let W : ℕ := Nat.card
    {w : Fin R → Fin H // ∀ h,
      Fintype.card {j // w j = h} = m}
  let E : ℝ := Real.exp 1
  let q : ℝ := ((((m : ℕ) : ℝ) / E) ^ m) ^ H
  let D : ℝ := (6 * (((m + 1 : ℕ) : ℝ))) ^ H
  have hR : 1 ≤ R := by
    dsimp [R]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hH.ne' hm.ne')
  have hm1 : 1 ≤ m := hm
  have hq : 0 < q := by
    dsimp [q, E]
    positivity
  have hlower := factorial_lower_coarse_balanced R hR
  have hupper := factorial_upper_coarse_balanced m hm1
  have hupperPow : ((m.factorial : ℝ) ^ H) ≤ D * q := by
    dsimp [D, q, E]
    calc
      (m.factorial : ℝ) ^ H ≤
          (6 * (((m + 1 : ℕ) : ℝ)) *
            (((m : ℕ) : ℝ) / Real.exp 1) ^ m) ^ H := by
        exact pow_le_pow_left₀ (by positivity) hupper H
      _ = (6 * (((m + 1 : ℕ) : ℝ))) ^ H *
          ((((m : ℕ) : ℝ) / Real.exp 1) ^ m) ^ H := by
        rw [mul_pow]
  have hdiv : (∏ _h : Fin H, m.factorial) ∣ (H * m).factorial := by
    have hsum : (∑ _h : Fin H, m) = H * m := by simp
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin H)) (fun _ : Fin H => m)
    rw [hsum] at h
    exact h
  have hidNat : W * m.factorial ^ H = R.factorial := by
    dsimp [W, R]
    rw [mme_Ctensor_balanced_word_card]
    have hprod : (∏ _h : Fin H, m.factorial) = m.factorial ^ H := by simp
    rw [← hprod, Nat.div_mul_cancel hdiv]
  have hidReal : (W : ℝ) * (m.factorial : ℝ) ^ H = (R.factorial : ℝ) := by
    exact_mod_cast hidNat
  have hpower : (H : ℝ) ^ R * q =
      (((R : ℕ) : ℝ) / E) ^ R := by
    dsimp [q, R, E]
    push_cast
    rw [show ((H : ℝ) * (m : ℝ) / Real.exp 1) =
        (H : ℝ) * ((m : ℝ) / Real.exp 1) by ring]
    rw [mul_pow, ← pow_mul]
    simp only [mul_comm]
  have hchain : (H : ℝ) ^ R * q ≤ D * (W : ℝ) * q := by
    rw [hpower]
    calc
      (((R : ℕ) : ℝ) / E) ^ R ≤ (R.factorial : ℝ) := by
        simpa [E] using hlower
      _ = (W : ℝ) * (m.factorial : ℝ) ^ H := hidReal.symm
      _ ≤ (W : ℝ) * (D * q) := by
        gcongr
      _ = D * (W : ℝ) * q := by ring
  have hcancel := le_of_mul_le_mul_right hchain hq
  simpa [D, W, R] using hcancel
