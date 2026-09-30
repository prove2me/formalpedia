-- Prove2me | solution 1 for lean_workbook_plus_73662
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:11:22.137715+00:00
-- url     : https://prove2.me/submissions/962df7a5-837a-4678-8f4b-30d2277b93e9

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

theorem recurrence_addition (a b : ℕ) (u : ℕ → ℕ)
    (hz : u 0 = 0) (ho : u 1 = 1)
    (hr : ∀ k, u (k + 2) = a * u (k + 1) + b * u k) (m k : ℕ) :
    u (m + (k + 1)) = u (m + 1) * u (k + 1) + b * u m * u k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [hz, ho]
  | one => simp [hr, hz, ho]; ring
  | more k ih ihn =>
    calc
      u (m + (k + 2 + 1)) = a * u (m + (k + 1 + 1)) + b * u (m + (k + 1)) := by
        convert hr (m + (k + 1)) using 1
      _ = a * (u (m + 1) * u (k + 1 + 1) + b * u m * u (k + 1)) +
          b * (u (m + 1) * u (k + 1) + b * u m * u k) := by rw [ihn, ih]
      _ = u (m + 1) * u (k + 2 + 1) + b * u m * u (k + 2) := by
        rw [show k + 2 + 1 = (k + 1) + 2 by omega, hr (k + 1), hr k]
        ring

theorem recurrence_adjacent_coprime (a b : ℕ) (hab : a.Coprime b) (u : ℕ → ℕ)
    (hz : u 0 = 0) (ho : u 1 = 1)
    (hr : ∀ k, u (k + 2) = a * u (k + 1) + b * u k) (n : ℕ) :
    b.Coprime (u (n + 1)) ∧ (u n).Coprime (u (n + 1)) := by
  induction n with
  | zero => simp [hz, ho]
  | succ n ih =>
    change b.Coprime (u (n + 2)) ∧ (u (n + 1)).Coprime (u (n + 2))
    rw [hr]
    constructor
    · exact (Nat.coprime_add_mul_left_right b (a * u (n + 1)) (u n)).mpr
        (hab.symm.mul_right ih.1)
    · rw [Nat.add_comm (a * u (n + 1)) (b * u n)]
      exact (Nat.coprime_add_mul_right_right (u (n + 1)) (b * u n) a).mpr
        (ih.1.symm.mul_right ih.2.symm)

theorem recurrence_zero_shift_iff (a b c : ℕ) (hab : a.Coprime b) (u : ℕ → ℕ)
    (hz : u 0 = 0) (ho : u 1 = 1)
    (hr : ∀ k, u (k + 2) = a * u (k + 1) + b * u k)
    (m : ℕ) (hm : c ∣ u m) (r : ℕ) :
    c ∣ u (m + r) ↔ c ∣ u r := by
  cases r with
  | zero => simp [hz, hm]
  | succ r =>
    rw [recurrence_addition a b u hz ho hr]
    have ht : c ∣ b * u m * u r :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hm b) (u r)
    have hc : c.Coprime (u (m + 1)) :=
      (recurrence_adjacent_coprime a b hab u hz ho hr m).2.of_dvd_left hm
    exact (Nat.dvd_add_iff_left ht).symm.trans hc.dvd_mul_left

theorem recurrence_rank_divides (a b c : ℕ) (hab : a.Coprime b) (u : ℕ → ℕ)
    (hz : u 0 = 0) (ho : u 1 = 1)
    (hr : ∀ k, u (k + 2) = a * u (k + 1) + b * u k)
    (m : ℕ) (hmpos : 0 < m) (hm : c ∣ u m)
    (hmin : ∀ k, 0 < k → c ∣ u k → m ≤ k) (n : ℕ) (hn : c ∣ u n) : m ∣ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnz : n = 0
    · simp [hnz]
    have hmn := hmin n (by omega) hn
    have he : m + (n - m) = n := by omega
    have hrzero : c ∣ u (n - m) :=
      (recurrence_zero_shift_iff a b c hab u hz ho hr m hm (n - m)).mp
        (by simpa only [he] using hn)
    have hd := ih (n - m) (by omega) hrzero
    have ha := Nat.dvd_add (dvd_refl m) hd
    simpa only [he] using ha

theorem recurrence_rank_classification (a b c : ℕ) (hab : a.Coprime b) (u : ℕ → ℕ)
    (hz : u 0 = 0) (ho : u 1 = 1)
    (hr : ∀ k, u (k + 2) = a * u (k + 1) + b * u k)
    (m : ℕ) (hmpos : 0 < m) (hm : c ∣ u m)
    (hmin : ∀ k, 0 < k → c ∣ u k → m ≤ k) (n : ℕ) :
    c ∣ u n ↔ m ∣ n := by
  constructor
  · exact recurrence_rank_divides a b c hab u hz ho hr m hmpos hm hmin n
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => simp [hz]
    | succ k ih =>
      rw [Nat.mul_succ, Nat.add_comm]
      exact (recurrence_zero_shift_iff a b c hab u hz ho hr m hm (m * k)).mpr ih

theorem solution (a b c : ℕ) (h1 : Nat.gcd a b = 1) (u : ℕ → ℕ)
    (h2 : u 0 = 0 ∧ u 1 = 1)
    (h3 : ∀ k, u (k + 2) = a * u (k + 1) + b * u k)
    (h4 : ∃ m, c ∣ u m) (h5 : ∃ n, c ∣ u n) :
    ∃ m n, c ∣ u m ∧ c ∣ u n → m ∣ n := by
  exact ⟨1, 1, fun _ => dvd_refl 1⟩
