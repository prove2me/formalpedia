-- Prove2me | solution 1 for mme_dwz_table2_retained_polynomial_denominator_le_exp_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T17:40:04.732484+00:00
-- url     : https://prove2.me/submissions/77027dd1-f2b3-43ac-b358-14b98c4e40e2

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

theorem solution
    (L : ℕ) :
    let x : ℝ := (((L + 1 : ℕ) : ℝ))
    let jointPoly : ℝ := (6 * x) ^ 15
    let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
    let zPoly : ℝ := (6 * x) ^ 5
    let compatibilityPoly : ℝ := (6 * x) ^ 9
    let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
    32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly) ≤
      Real.exp (B * Real.sqrt x) := by
  dsimp only
  let x : ℝ := (((L + 1 : ℕ) : ℝ))
  let y : ℝ := Real.sqrt x
  let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
  have hx1 : (1 : ℝ) ≤ x := by
    dsimp only [x]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le L)
  have hx0 : 0 ≤ x := hx1.trans' (by norm_num)
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hy2 : y ^ 2 = x := by
    dsimp only [y]
    exact Real.sq_sqrt hx0
  have hy70 : y ^ 70 = x ^ 35 := by
    calc
      y ^ 70 = (y ^ 2) ^ 35 := by norm_num [← pow_mul]
      _ = x ^ 35 := by rw [hy2]
  have hx14 : (1 : ℝ) ≤ x ^ 14 := one_le_pow₀ hx1
  have hx21 : (1 : ℝ) ≤ x ^ 21 := one_le_pow₀ hx1
  have h6six : (1 : ℝ) ≤ (6 : ℝ) ^ 6 := one_le_pow₀ (by norm_num)
  have hfactor : (1 : ℝ) ≤ 6 ^ 6 * x ^ 21 :=
    one_le_mul_of_one_le_of_one_le h6six hx21
  have hsmallNonneg : (0 : ℝ) ≤ 6 ^ 14 * x ^ 14 := by positivity
  have hbranch : (6 * x) ^ 5 * (6 * x) ^ 9 ≤
      (6 * x) ^ 15 * ((6 * x) ^ 5 * x ^ 15) := by
    calc
      (6 * x) ^ 5 * (6 * x) ^ 9 = 6 ^ 14 * x ^ 14 := by ring
      _ ≤ (6 ^ 14 * x ^ 14) * (6 ^ 6 * x ^ 21) :=
        le_mul_of_one_le_right hsmallNonneg hfactor
      _ = (6 * x) ^ 15 * ((6 * x) ^ 5 * x ^ 15) := by ring
  rw [max_eq_left hbranch]
  have hfacNat : 1 ≤ (70 : ℕ).factorial :=
    Nat.one_le_of_lt (Nat.factorial_pos 70)
  have hfac : (1 : ℝ) ≤ ((70 : ℕ).factorial : ℝ) := by exact_mod_cast hfacNat
  have h32 : (1 : ℝ) ≤ 32 := by norm_num
  have h620 : (1 : ℝ) ≤ (6 : ℝ) ^ 20 := one_le_pow₀ (by norm_num)
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp only [B]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h32 h620) hfac
  have hB0 : 0 ≤ B := hB1.trans' (by norm_num)
  have hBpow69 : (1 : ℝ) ≤ B ^ 69 := one_le_pow₀ hB1
  have hBpow : B ≤ B ^ 70 := by
    calc
      B = B * 1 := by ring
      _ ≤ B * B ^ 69 := by gcongr
      _ = B ^ 70 := by ring
  have hpoly :
      (32 * ((6 * x) ^ 15 * ((6 * x) ^ 5 * x ^ 15))) *
          ((70 : ℕ).factorial : ℝ) ≤ (B * y) ^ 70 := by
    calc
      (32 * ((6 * x) ^ 15 * ((6 * x) ^ 5 * x ^ 15))) *
            ((70 : ℕ).factorial : ℝ) = B * y ^ 70 := by
        rw [hy70]
        dsimp only [B]
        ring
      _ ≤ B ^ 70 * y ^ 70 := by gcongr
      _ = (B * y) ^ 70 := by ring
  calc
    32 * ((6 * x) ^ 15 * ((6 * x) ^ 5 * x ^ 15)) ≤
        (B * y) ^ 70 / ((70 : ℕ).factorial : ℝ) := by
      apply (le_div_iff₀ (by positivity :
        (0 : ℝ) < ((70 : ℕ).factorial : ℝ))).2
      simpa only [mul_assoc] using hpoly
    _ ≤ Real.exp (B * y) :=
      Real.pow_div_factorial_le_exp (B * y) (mul_nonneg hB0 hy0) 70
    _ = Real.exp (B * Real.sqrt x) := by rfl
