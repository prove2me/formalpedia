-- Prove2me | solution 1 for lean_workbook_plus_12210
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:27:39.970112+00:00
-- url     : https://prove2.me/submissions/470cc77c-b307-4ba6-8560-faaf374c317c

import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace EvenBaseTower

theorem odd_shift_square (b : ℤ) (s : ℕ) :
    b ^ 2 ∣ (b - 1) ^ (2 * s + 1) + 1 - (2 * (s : ℤ) + 1) * b := by
  induction s with
  | zero =>
    convert dvd_zero (b ^ 2) using 1
    ring
  | succ s ih =>
    obtain ⟨w, hw⟩ := ih
    have hp : (b - 1) ^ (2 * s + 1) = b ^ 2 * w - 1 + (2 * (s : ℤ) + 1) * b := by
      nlinarith [hw]
    refine ⟨w * (b - 1) ^ 2 + (2 * (s : ℤ) + 1) * b - (4 * (s : ℤ) + 3), ?_⟩
    rw [show 2 * (s + 1) + 1 = (2 * s + 1) + 2 by omega, pow_add, hp]
    push_cast
    ring

theorem one_step (k A B : ℕ) (hB : Odd B) (hrel : B = k ^ A + 1)
    (hAB : A ∣ B) : B ∣ k ^ B + 1 ∧ B ^ 2 ∣ A * (k ^ B + 1) := by
  obtain ⟨r, hr⟩ := hAB
  have hro : Odd r := Nat.Odd.of_mul_right (hr ▸ hB)
  obtain ⟨s, hs⟩ := hro
  have hs' : r = 2 * s + 1 := by omega
  have hr' : B = A * (2 * s + 1) := by rwa [hs'] at hr
  have hrz : (B : ℤ) = (A : ℤ) * (2 * (s : ℤ) + 1) := by exact_mod_cast hr'
  have hkz : (k : ℤ) ^ A = (B : ℤ) - 1 := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hrel
    push_cast at h
    omega
  have hp : (k : ℤ) ^ B = ((B : ℤ) - 1) ^ (2 * s + 1) := by
    conv_lhs => rw [hr', pow_mul, hkz]
  have hd := odd_shift_square (B : ℤ) s
  rw [← hp] at hd
  have hBB : (B : ℤ) ∣ (B : ℤ) ^ 2 := ⟨B, by ring⟩
  have hlin : (B : ℤ) ∣ (2 * (s : ℤ) + 1) * B := ⟨2 * (s : ℤ) + 1, by ring⟩
  have hchain : (B : ℤ) ∣ (k : ℤ) ^ B + 1 := by
    simpa only [sub_add_cancel] using dvd_add (hBB.trans hd) hlin
  have hmul : (B : ℤ) ^ 2 ∣
      (A : ℤ) * ((k : ℤ) ^ B + 1 - (2 * (s : ℤ) + 1) * B) :=
    dvd_mul_of_dvd_right hd A
  have hsquare : (B : ℤ) ^ 2 ∣ (A : ℤ) * ((k : ℤ) ^ B + 1) := by
    have h := dvd_add hmul (dvd_rfl : (B : ℤ) ^ 2 ∣ (B : ℤ) ^ 2)
    convert h using 1 <;> rw [hrz] <;> ring
  exact ⟨by exact_mod_cast hchain, by exact_mod_cast hsquare⟩

theorem next_odd (k A : ℕ) (hk : 2 ∣ k) (hA : 0 < A) : Odd (k ^ A + 1) := by
  have hd : 2 ∣ k ^ A := dvd_pow hk (by omega)
  apply Nat.odd_iff.mpr
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]

theorem chain (k : ℕ) (hk : 2 ∣ k) (x : ℕ → ℕ) (hx : x 1 = 1)
    (hnext : ∀ n, 1 ≤ n → x (n + 1) = k ^ x n + 1) (n : ℕ) :
    0 < x (n + 1) ∧ Odd (x (n + 1)) ∧ x (n + 1) ∣ x (n + 2) := by
  induction n with
  | zero => simp [hx]
  | succ n ih =>
    change 0 < x (n + 2) ∧ Odd (x (n + 2)) ∧ x (n + 2) ∣ x (n + 3)
    have hB := hnext (n + 1) (by omega)
    have hC := hnext (n + 2) (by omega)
    have hodd : Odd (x (n + 2)) := by rw [hB]; exact next_odd k _ hk ih.1
    refine ⟨by rw [hB]; omega, hodd, ?_⟩
    rw [hC]
    exact (one_step k (x (n + 1)) (x (n + 2)) hodd hB ih.2.2).1

theorem adjacent_square (k : ℕ) (hk : 2 ∣ k) (x : ℕ → ℕ) (hx : x 1 = 1)
    (hnext : ∀ n, 1 ≤ n → x (n + 1) = k ^ x n + 1) (n : ℕ) (hn : 2 ≤ n) :
    (x n) ^ 2 ∣ x (n - 1) * x (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hA := chain k hk x hx hnext m
  have hB := chain k hk x hx hnext (m + 1)
  have hd := (one_step k (x (m + 1)) (x (m + 2)) hB.2.1
    (hnext (m + 1) (by omega)) hA.2.2).2
  rw [show m + 2 - 1 = m + 1 by omega]
  rw [hnext (m + 2) (by omega)]
  exact hd

def orbit (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => k ^ orbit k n + 1

theorem positive_index_model (k : ℕ) :
    ∃ x : ℕ → ℕ, x 1 = 1 ∧ ∀ n, 1 ≤ n → x (n + 1) = k ^ x n + 1 := by
  refine ⟨fun n => orbit k (n - 1), rfl, ?_⟩
  intro n hn
  simp only [Nat.add_sub_cancel]
  have h : orbit k ((n - 1) + 1) = k ^ orbit k (n - 1) + 1 := rfl
  simpa only [Nat.sub_add_cancel hn] using h

end EvenBaseTower

theorem solution (k : ℕ) (x : ℕ → ℕ) (h₀ : x 1 = 1)
    (h₁ : ∀ n, x (n + 1) = k ^ x n + 1) (h₂ : 2 ∣ k) (n : ℕ) (hn : 2 ≤ n) :
    (x n) ^ 2 ∣ (x (n - 1)) * (x (n + 1)) :=
  EvenBaseTower.adjacent_square k h₂ x h₀ (fun n _ => h₁ n) n hn
