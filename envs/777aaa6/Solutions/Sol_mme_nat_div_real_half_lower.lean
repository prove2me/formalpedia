-- Prove2me | solution 1 for mme_nat_div_real_half_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:09:46.506277+00:00
-- url     : https://prove2.me/submissions/69291088-ab75-4125-9fb1-a592ce1a7ac5

import Mathlib

theorem solution
    {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    (n : ℝ) / (2 * (d : ℝ)) ≤ ((n / d : ℕ) : ℝ) := by
  have hq : 0 < n / d := Nat.div_pos hdn hd
  have hmod : n % d ≤ d := (Nat.mod_lt n hd).le
  have hdq : d ≤ d * (n / d) := by
    calc
      d = d * 1 := by simp
      _ ≤ d * (n / d) := Nat.mul_le_mul_left d hq
  have hn : n ≤ 2 * d * (n / d) := by
    calc
      n = d * (n / d) + n % d := (Nat.div_add_mod n d).symm
      _ ≤ d * (n / d) + d := Nat.add_le_add_left hmod _
      _ ≤ d * (n / d) + d * (n / d) := Nat.add_le_add_left hdq _
      _ = 2 * d * (n / d) := by ring
  have hn' : n ≤ (n / d) * (2 * d) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hn
  have hden : 0 < (2 : ℝ) * (d : ℝ) :=
    mul_pos (by norm_num) (by exact_mod_cast hd)
  rw [div_le_iff₀ hden]
  exact_mod_cast hn'
