-- Prove2me | solution 1 for lean_workbook_plus_39881
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:33:29.974966+00:00
-- url     : https://prove2.me/submissions/0bd5e992-6de1-494e-b55d-5626b1464faa

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum

def balancedDivisorCount (n : ℕ) : Prop :=
  ((n - 1).divisors.card ≤ n.divisors.card ∧ n.divisors.card ≤ (n + 1).divisors.card) ∨
  (n.divisors.card ≤ (n - 1).divisors.card ∧ (n + 1).divisors.card ≤ n.divisors.card)

private theorem three_le_even_divisor_count (n : ℕ) (hn : 2 < n) (he : Even n) :
    3 ≤ n.divisors.card := by
  have hsub : ({1, 2, n} : Finset ℕ) ⊆ n.divisors := by
    intro k hk
    apply Nat.mem_divisors.mpr
    refine ⟨?_, by omega⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact one_dvd _
    · exact even_iff_two_dvd.mp he
    · exact dvd_refl _
  have hc : ({1, 2, n} : Finset ℕ).card = 3 := by
    simp [show 1 ≠ n by omega, show 2 ≠ n by omega]
  rw [← hc]
  exact Finset.card_le_card hsub

private theorem five_le_fifteen_multiple_divisor_count (n : ℕ) (hn : 15 < n)
    (hd : 15 ∣ n) : 5 ≤ n.divisors.card := by
  have hsub : ({1, 3, 5, 15, n} : Finset ℕ) ⊆ n.divisors := by
    intro k hk
    apply Nat.mem_divisors.mpr
    refine ⟨?_, by omega⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact dvd_trans (by decide : 3 ∣ 15) hd
    · exact dvd_trans (by decide : 5 ∣ 15) hd
    · exact hd
    · exact dvd_refl _
  have hc : ({1, 3, 5, 15, n} : Finset ℕ).card = 5 := by
    simp [show 1 ≠ n by omega, show 3 ≠ n by omega,
      show 5 ≠ n by omega, show 15 ≠ n by omega]
  rw [← hc]
  exact Finset.card_le_card hsub

theorem balanced_divisor_counts_unbounded (N : ℕ) :
    ∃ n : ℕ, N < n ∧ balancedDivisorCount n := by
  let d : ℕ → ℕ := fun n => n.divisors.card
  by_contra hnot
  have hbad : ∀ n, N < n → ¬ ((d (n - 1) ≤ d n ∧ d n ≤ d (n + 1)) ∨
      (d n ≤ d (n - 1) ∧ d (n + 1) ≤ d n)) := by
    intro n hn h
    exact hnot ⟨n, hn, h⟩
  obtain ⟨q, hqN, hq, hqmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (N + 3) (q := 2) (a := 1) (by decide) (by decide)
  have hqodd : q % 2 = 1 := by simpa [Nat.ModEq] using hqmod
  have hdq : d q = 2 := by
    dsimp [d]
    rw [hq.divisors]
    simp [hq.ne_one.symm]
  have hdq1 : 3 ≤ d (q + 1) := three_le_even_divisor_count (q + 1) (by omega)
    (even_iff_two_dvd.mpr (by omega))
  have hstart : d q < d (q + 1) := by omega
  have hstep : ∀ n, q ≤ n → d n < d (n + 1) → d (n + 2) < d (n + 3) := by
    intro n hn hdn
    have hb1 := hbad (n + 1) (by omega)
    have hb2 := hbad (n + 2) (by omega)
    rw [show n + 1 - 1 = n by omega, show n + 1 + 1 = n + 2 by omega] at hb1
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 + 1 = n + 3 by omega] at hb2
    omega
  have hrun : ∀ k : ℕ, d (q + 2 * k) < d (q + 2 * k + 1) := by
    intro k
    induction k with
    | zero => simpa using hstart
    | succ k ih =>
      have hs := hstep (q + 2 * k) (by omega) ih
      convert hs using 1
  obtain ⟨p, hpq, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (q + 15) (q := 15) (a := 8) (by decide) (by decide)
  have hp8 : p % 15 = 8 := by simpa [Nat.ModEq] using hpmod
  have hcop : Nat.Coprime 2 p :=
    (hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p))).symm
  have hd2p : d (2 * p) = 4 := by
    dsimp [d]
    rw [hcop.card_divisors_mul, Nat.prime_two.divisors, hp.divisors]
    simp [hp.ne_one.symm]
  have hlow : 5 ≤ d (2 * p - 1) :=
    five_le_fifteen_multiple_divisor_count (2 * p - 1) (by omega) (by omega)
  have hrepr : 2 * p - 1 = q + 2 * ((2 * p - 1 - q) / 2) := by omega
  have hinc := hrun ((2 * p - 1 - q) / 2)
  rw [← hrepr, show 2 * p - 1 + 1 = 2 * p by omega] at hinc
  omega

theorem balanced_divisor_counts_infinite :
    {n : ℕ | 0 < n ∧ balancedDivisorCount n}.Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  obtain ⟨n, hn, hb⟩ := balanced_divisor_counts_unbounded N
  exact ⟨n, ⟨by omega, hb⟩, hn⟩

theorem solution (d : ℕ → ℕ) (hd : d = fun k => (Nat.divisors k).card) :
    ∃ n, (d (n - 1) ≤ d n ∧ d n ≤ d (n + 1)) ∨
      (d (n - 1) ≥ d n ∧ d n ≥ d (n + 1)) := by
  obtain ⟨n, _, hn⟩ := balanced_divisor_counts_infinite.nonempty
  subst d
  exact ⟨n, hn⟩
