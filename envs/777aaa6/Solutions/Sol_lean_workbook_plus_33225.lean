-- Prove2me | solution 1 for lean_workbook_plus_33225
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:36:32.680978+00:00
-- url     : https://prove2.me/submissions/6947e9c3-4cae-4fcb-99ee-7fa48460adbf

import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Ring

theorem weighted_power_linear_remainder (a t d : ℤ)
    (h : d ∣ t * (a - 1) ^ 2) (n : ℕ) :
    d ∣ t * a ^ n - t - n * t * (a - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      convert dvd_add (ih.mul_left a) (h.mul_left (n : ℤ)) using 1 <;>
        simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring

theorem weighted_exponential_linear_divisibility (a t b c d : ℤ) :
    (∀ n : ℕ, d ∣ t * a ^ n + b * n + c) ↔
      d ∣ t + c ∧ d ∣ t * (a - 1) + b ∧ d ∣ t * (a - 1) ^ 2 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    norm_num only [pow_zero, pow_one, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
      mul_zero, mul_one, add_zero] at h0 h1 h2
    refine ⟨h0, ?_, ?_⟩
    · convert dvd_sub h1 h0 using 1 <;> ring
    · convert dvd_add (dvd_sub h2 (h1.mul_left 2)) h0 using 1 <;> ring
  · rintro ⟨hc, hb, ha⟩ n
    have hrem := weighted_power_linear_remainder a t d ha n
    convert dvd_add (dvd_add hrem (hb.mul_left (n : ℤ))) hc using 1 <;> ring

theorem exponential_linear_divisibility (a b c d : ℤ) :
    (∀ n : ℕ, d ∣ a ^ n + b * n + c) ↔
      d ∣ c + 1 ∧ d ∣ a + b - 1 ∧ d ∣ (a - 1) ^ 2 := by
  simpa only [one_mul, add_comm 1 c, sub_add_eq_add_sub] using
    weighted_exponential_linear_divisibility a 1 b c d

theorem positive_exponential_linear_divisibility (a b c d : ℤ) :
    (∀ n : ℕ, 0 < n → d ∣ a ^ n + b * n + c) ↔
      d ∣ a + b + c ∧ d ∣ a * (a - 1) + b ∧ d ∣ a * (a - 1) ^ 2 := by
  have hshift : (∀ n : ℕ, 0 < n → d ∣ a ^ n + b * n + c) ↔
      ∀ n : ℕ, d ∣ a * a ^ n + b * n + (b + c) := by
    constructor
    · intro h n
      convert h (n + 1) (by omega) using 1 <;> push_cast <;> ring
    · intro h n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      convert h k using 1 <;> simp only [pow_succ, Nat.cast_succ] <;> ring
  rw [hshift]
  simpa only [add_assoc] using weighted_exponential_linear_divisibility a a b (b + c) d

theorem solution (a b c d : ℤ) (n : ℕ) :
    (a ^ n + b * n + c) % d = 0 ↔ d ∣ a ^ n + b * n + c :=
  Int.dvd_iff_emod_eq_zero.symm
