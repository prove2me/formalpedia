-- Prove2me | solution 1 for mme_dwz_common_prime_le_exp_sixteen_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T17:45:33.816527+00:00
-- url     : https://prove2.me/submissions/8c77449b-d932-416e-bf51-402d797a5d8d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (L d Q p : ℕ)
    (hd : d ≤ 15 ^ L) (hQ : Q ≤ 15 ^ L)
    (hp : p ≤ 2 * max 4 (8 * max d Q)) :
    (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) := by
  have hmax : max d Q ≤ 15 ^ L := max_le hd hQ
  have hpow : 1 ≤ 15 ^ L := one_le_pow₀ (by decide)
  have hbudget : max 4 (8 * max d Q) ≤ 8 * 15 ^ L := by
    apply max_le
    · omega
    · omega
  have hpNat : p ≤ 16 * 15 ^ L := by
    calc
      p ≤ 2 * max 4 (8 * max d Q) := hp
      _ ≤ 2 * (8 * 15 ^ L) := Nat.mul_le_mul_left 2 hbudget
      _ = 16 * 15 ^ L := by ring
  have hpReal : (p : ℝ) ≤ 16 * (15 : ℝ) ^ L := by
    exact_mod_cast hpNat
  have h15exp : (15 : ℝ) ≤ Real.exp 16 := by
    have hexp := Real.add_one_le_exp (16 : ℝ)
    norm_num at hexp
    calc
      (15 : ℝ) ≤ 17 := by norm_num
      _ ≤ Real.exp 16 := hexp
  have h16exp : (16 : ℝ) ≤ Real.exp 16 := by
    have hexp := Real.add_one_le_exp (16 : ℝ)
    norm_num at hexp
    calc
      (16 : ℝ) ≤ 17 := by norm_num
      _ ≤ Real.exp 16 := hexp
  have hpowexp : (15 : ℝ) ^ L ≤ (Real.exp 16) ^ L := by gcongr
  calc
    (p : ℝ) ≤ 16 * (15 : ℝ) ^ L := hpReal
    _ ≤ Real.exp 16 * (Real.exp 16) ^ L := by gcongr
    _ = Real.exp 16 * Real.exp ((L : ℝ) * 16) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (16 + (L : ℝ) * 16) := by rw [Real.exp_add]
    _ = Real.exp (16 * (((L + 1 : ℕ) : ℝ))) := by
      congr 1
      push_cast
      ring
