-- Prove2me | solution 1 for lean_workbook_plus_64318
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:58:53.294666+00:00
-- url     : https://prove2.me/submissions/582f1285-4ec8-4f10-9ad0-9e3152243a6f

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

private theorem twice_half (n : ℕ) : n * (n + 3) / 2 * 2 = n * (n + 3) := by
  apply Nat.div_mul_cancel
  obtain ⟨q, hq⟩ := (Nat.even_mul_succ_self n).two_dvd
  exact ⟨q + n, by nlinarith⟩

theorem feasibility_iff (n : ℕ) :
    (∃ A B : ℕ, A + B = n * (2 * n + 1) ∧
      A - B = n * (n + 3) / 2) ↔ 4 ∣ n * (n + 1) := by
  constructor
  · rintro ⟨A, B, hsum, hdiff⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hge : 2 ≤ n * (n + 3) := by nlinarith
    have hpos : 0 < A - B := by
      rw [hdiff]
      exact Nat.div_pos hge (by decide)
    have hBA : B ≤ A := Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hpos)
    have hsub := Nat.sub_add_cancel hBA
    have hh := twice_half n
    have hlinear : 3 * (n * (n + 1)) = 4 * (B + n) := by nlinarith
    exact (by decide : Nat.Coprime 4 3).dvd_of_dvd_mul_left ⟨B + n, hlinear⟩
  · rintro ⟨q, hq⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, 0, by simp⟩
    have hnq : n ≤ 3 * q := by nlinarith
    have hsub := Nat.sub_add_cancel hnq
    have hBA : 3 * q - n ≤ 5 * q := by omega
    have hsubA := Nat.sub_add_cancel hBA
    refine ⟨5 * q, 3 * q - n, ?_, ?_⟩
    · nlinarith
    · have hh := twice_half n
      nlinarith

theorem solution (n : ℕ) (_hn : 0 < n)
    (h : ∃ A B : ℕ, A + B = n * (2 * n + 1) ∧
      A - B = n * (n + 3) / 2) : 4 ∣ n * (n + 1) :=
  (feasibility_iff n).mp h
