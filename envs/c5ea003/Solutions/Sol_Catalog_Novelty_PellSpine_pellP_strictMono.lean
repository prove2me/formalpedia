-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellP_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T20:49:11.087544+00:00
-- url     : https://prove2.me/submissions/d49c0ca2-516f-49be-a3da-d777674cbd01

import Mathlib
import Definitions.Def_Novelty_PellSpineCore
open Catalog.Novelty.PellSpine Finset in
theorem solution : StrictMono pellP := by
  have hP0 : pellP 0 = 0 := rfl
  have hQ0 : pellQ 0 = 1 := rfl
  have hstep : ∀ n, pellP (n + 1) = pellP n + pellQ n ∧ pellQ (n + 1) = pellQ n + 2 * pellP n := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      have e1 : pellP (n + 1 + 1) = 2 * pellP (n + 1) + pellP n := rfl
      have e2 : pellQ (n + 1 + 1) = 2 * pellQ (n + 1) + pellQ n := rfl
      constructor <;> omega
  have hadd : ∀ m n, pellP (m + n) = pellP m * pellQ n + pellQ m * pellP n ∧
      pellQ (m + n) = pellQ m * pellQ n + 2 * (pellP m * pellP n) := by
    intro m n
    induction n with
    | zero => simp [hP0, hQ0]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨s1, s2⟩ := hstep (m + n)
      obtain ⟨t1, t2⟩ := hstep n
      rw [← add_assoc, s1, s2, h1, h2, t1, t2]
      constructor <;> ring
  have heq : ∀ n, (pellQ n : ℤ) ^ 2 - 2 * (pellP n : ℤ) ^ 2 = (-1) ^ n := by
    intro n
    induction n with
    | zero => simp [hP0, hQ0]
    | succ n ih =>
      obtain ⟨s1, s2⟩ := hstep n
      rw [s1, s2, pow_succ (-1 : ℤ) n, ← ih]
      push_cast
      ring
  have hcop : ∀ n, Nat.Coprime (pellP n) (pellQ n) := by
    intro n
    rw [← Nat.isCoprime_iff_coprime]
    refine ⟨(-1) ^ n * (-2 * (pellP n : ℤ)), (-1) ^ n * (pellQ n : ℤ), ?_⟩
    have h := heq n
    have h2 : ((-1 : ℤ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    linear_combination (-1 : ℤ) ^ n * h + h2
  have hQpos : ∀ n, 1 ≤ pellQ n := by
    intro n
    induction n with
    | zero => simp [hQ0]
    | succ n ih => rw [(hstep n).2]; omega
  have hPlt : ∀ n, pellP n < pellP (n + 1) := by
    intro n
    rw [(hstep n).1]
    have := hQpos n
    omega
  have hPmono : StrictMono pellP := strictMono_nat_of_lt_succ hPlt
  have hPinj : Function.Injective pellP := hPmono.injective
  have hPpos : ∀ n, 1 ≤ n → 0 < pellP n := by
    intro n hn
    have := hPmono (show 0 < n by omega)
    rwa [hP0] at this
  have hQodd : ∀ n, Odd (pellQ n) := by
    intro n
    induction n with
    | zero => simp [hQ0]
    | succ n ih => rw [(hstep n).2]; exact ih.add_even (even_two_mul _)
  have hQlt : ∀ n, 1 ≤ n → pellQ n < pellQ (n + 1) := by
    intro n hn
    rw [(hstep n).2]
    have := hPpos n hn
    omega
  have hQmono : ∀ a k, 1 ≤ a → pellQ a < pellQ (a + k + 1) := by
    intro a k ha
    induction k with
    | zero => exact hQlt a ha
    | succ k ih => exact ih.trans (hQlt _ (by omega))
  have hP2m : ∀ k, pellP (2 * k) = 2 * (pellP k * pellQ k) := by
    intro k
    rw [two_mul, (hadd k k).1]
    ring
  have hgcd_add : ∀ m n, Nat.gcd (pellP m) (pellP (n + m)) = Nat.gcd (pellP m) (pellP n) := by
    intro m n
    rw [(hadd n m).1, Nat.gcd_add_mul_right_right, Nat.Coprime.gcd_mul_right_cancel_right]
    exact (hcop m).symm
  have hgcd_addmul : ∀ m n k, Nat.gcd (pellP m) (pellP (n + k * m)) = Nat.gcd (pellP m) (pellP n) := by
    intro m n k
    induction k with
    | zero => simp
    | succ k ih => rw [show n + (k + 1) * m = (n + k * m) + m by ring, hgcd_add, ih]
  have hPgcd : ∀ m n, Nat.gcd (pellP m) (pellP n) = pellP (Nat.gcd m n) := by
    intro m n
    induction m, n using Nat.gcd.induction with
    | H0 n => simp [hP0]
    | H1 m n hm ih =>
      rw [Nat.gcd_rec m n, ← ih, Nat.gcd_comm (pellP (n % m)), ← hgcd_addmul m (n % m) (n / m),
        Nat.mod_add_div' n m]
  have hPdvd : ∀ m n, m ∣ n ↔ pellP m ∣ pellP n := by
    intro m n
    rw [← Nat.gcd_eq_left_iff_dvd, ← Nat.gcd_eq_left_iff_dvd, hPgcd]
    exact ⟨fun h => by rw [h], fun h => hPinj h⟩
  have hQgcd_dvd : ∀ m n, Nat.gcd (pellQ m) (pellQ n) ∣ pellQ (Nat.gcd m n) := by
    intro m n
    have hdm : Nat.gcd (pellQ m) (pellQ n) ∣ pellQ m := Nat.gcd_dvd_left _ _
    have hdn : Nat.gcd (pellQ m) (pellQ n) ∣ pellQ n := Nat.gcd_dvd_right _ _
    have h1 : Nat.gcd (pellQ m) (pellQ n) ∣ pellP (2 * m) := by
      rw [hP2m]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hdm _) _
    have h2 : Nat.gcd (pellQ m) (pellQ n) ∣ pellP (2 * n) := by
      rw [hP2m]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hdn _) _
    have h3 : Nat.gcd (pellQ m) (pellQ n) ∣ pellP (Nat.gcd (2 * m) (2 * n)) := by
      rw [← hPgcd]
      exact Nat.dvd_gcd h1 h2
    rw [Nat.gcd_mul_left, hP2m] at h3
    have hodd : Nat.Coprime (Nat.gcd (pellQ m) (pellQ n)) 2 :=
      Nat.coprime_two_right.mpr (Odd.of_dvd_nat (hQodd m) hdm)
    have h4 : Nat.gcd (pellQ m) (pellQ n) ∣ pellP (Nat.gcd m n) * pellQ (Nat.gcd m n) :=
      hodd.dvd_of_dvd_mul_left h3
    have hdP : Nat.Coprime (Nat.gcd (pellQ m) (pellQ n)) (pellP (Nat.gcd m n)) := by
      have hg : pellP (Nat.gcd m n) ∣ pellP m := (hPdvd _ m).mp (Nat.gcd_dvd_left m n)
      exact Nat.Coprime.coprime_dvd_right hg (Nat.Coprime.coprime_dvd_left hdm (hcop m).symm)
    exact hdP.dvd_of_dvd_mul_left h4
  have hQ2mod : ∀ m a, pellQ (a + 2 * m) ≡ 2 * pellP m ^ 2 * pellQ a [MOD pellQ m] := by
    intro m a
    have h2m : 2 * m = m + m := two_mul m
    have e : pellQ (a + 2 * m) =
        2 * pellP m ^ 2 * pellQ a + pellQ m * (pellQ a * pellQ m + 4 * pellP a * pellP m) := by
      rw [(hadd a (2 * m)).2, h2m, (hadd m m).1, (hadd m m).2]
      ring
    unfold Nat.ModEq
    rw [e, Nat.add_mul_mod_self_left]
  have hQeven : ∀ m j, pellQ (2 * j * m) ≡ (2 * pellP m ^ 2) ^ j [MOD pellQ m] := by
    intro m j
    induction j with
    | zero =>
      simp only [mul_zero, zero_mul, hQ0, pow_zero]
      exact Nat.ModEq.refl _
    | succ j ih =>
      rw [show 2 * (j + 1) * m = 2 * j * m + 2 * m by ring, pow_succ]
      calc pellQ (2 * j * m + 2 * m) ≡ 2 * pellP m ^ 2 * pellQ (2 * j * m) [MOD pellQ m] :=
            hQ2mod m _
        _ ≡ 2 * pellP m ^ 2 * (2 * pellP m ^ 2) ^ j [MOD pellQ m] := Nat.ModEq.mul_left _ ih
        _ = (2 * pellP m ^ 2) ^ j * (2 * pellP m ^ 2) := by ring
  have hQodd_mul : ∀ n k, pellQ n ∣ pellQ ((2 * k + 1) * n) := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (2 * (k + 1) + 1) * n = (2 * k + 1) * n + 2 * n by ring]
      have h1 := hQ2mod n ((2 * k + 1) * n)
      have h2 : pellQ ((2 * k + 1) * n) ≡ 0 [MOD pellQ n] := Nat.modEq_zero_iff_dvd.mpr ih
      have h3 := h1.trans (h2.mul_left (2 * pellP n ^ 2))
      rw [mul_zero] at h3
      exact Nat.modEq_zero_iff_dvd.mp h3
  have hQcopP2 : ∀ m j, Nat.Coprime (pellQ m) ((2 * pellP m ^ 2) ^ j) := by
    intro m j
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.mul_right
    · exact Nat.coprime_two_right.mpr (hQodd m)
    · exact (hcop m).symm.pow_right 2
  have hQidx : ∀ m n, 2 ≤ m → pellQ m ∣ pellQ n → m ∣ n := by
    intro m n hm h
    have h1 : pellQ m ∣ pellQ (Nat.gcd m n) := by
      have := hQgcd_dvd m n
      rwa [Nat.gcd_eq_left h] at this
    by_contra hmn
    have hne : Nat.gcd m n ≠ m := fun e => hmn (by rw [← e]; exact Nat.gcd_dvd_right m n)
    have hlt : Nat.gcd m n < m :=
      lt_of_le_of_ne (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left m n)) hne
    have hle := Nat.le_of_dvd (by have := hQpos (Nat.gcd m n); omega) h1
    rcases Nat.eq_zero_or_pos (Nat.gcd m n) with h0 | h0
    · rw [Nat.gcd_eq_zero_iff] at h0
      omega
    · have := hQmono (Nat.gcd m n) (m - Nat.gcd m n - 1) h0
      rw [show Nat.gcd m n + (m - Nat.gcd m n - 1) + 1 = m by omega] at this
      omega
  have hQdvd_iff : ∀ m n, 2 ≤ m → (pellQ m ∣ pellQ n ↔ ∃ k, Odd k ∧ n = m * k) := by
    intro m n hm
    constructor
    · intro h
      obtain ⟨k, rfl⟩ := hQidx m n hm h
      refine ⟨k, ?_, rfl⟩
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hk
      · exfalso
        rw [show m * (j + j) = 2 * j * m by ring] at h
        have h2 : pellQ m ∣ (2 * pellP m ^ 2) ^ j := ((hQeven m j).dvd_iff dvd_rfl).mp h
        have h3 := Nat.Coprime.eq_one_of_dvd (hQcopP2 m j) h2
        have h4 := hQmono 1 (m - 2) (le_refl 1)
        rw [show 1 + (m - 2) + 1 = m by omega] at h4
        have : pellQ 1 = 1 := rfl
        omega
      · exact hk
    · rintro ⟨k, ⟨j, rfl⟩, rfl⟩
      rw [show m * (2 * j + 1) = (2 * j + 1) * m by ring]
      exact hQodd_mul m j
  exact hPmono
