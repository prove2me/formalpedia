-- Prove2me | solution 1 for lean_workbook_plus_77624
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:09:05.029118+00:00
-- url     : https://prove2.me/submissions/3fd45834-7302-4405-8c25-602eda471649

import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

open Finset

theorem dyadic_free_positive_bound (n : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ n)
    (hpow : ∀ k : ℕ, 2 ^ k ∉ S)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ k : ℕ, x + y ≠ 2 ^ k) :
    2 * S.card ≤ n - 1 := by
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hn : n = 0
    · have he : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have := hS x hx
        omega
      simp [he]
    let q := 2 ^ Nat.log 2 n
    have hq : q ≤ n := Nat.pow_log_le_self 2 hn
    have hnq : n < 2 * q := by
      simpa [q, pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
    have hqpos : 0 < q := Nat.pow_pos (by decide)
    let m := 2 * q - n - 1
    have hmn : m < n := by dsimp [m]; omega
    let L := S.filter (fun x => x ≤ m)
    let H := S.filter (fun x => ¬ x ≤ m)
    have hL : ∀ x ∈ L, 1 ≤ x ∧ x ≤ m := by
      intro x hx
      exact ⟨(hS x (mem_filter.mp hx).1).1, (mem_filter.mp hx).2⟩
    have hLpow : ∀ k : ℕ, 2 ^ k ∉ L := by
      intro k hk
      exact hpow k (mem_filter.mp hk).1
    have hLpair : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → ∀ k : ℕ, x + y ≠ 2 ^ k := by
      intro x hx y hy
      exact hpair x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
    have hlow := ih m hmn L hL hLpow hLpair
    -- Reflection pairs the upper interval, with the forbidden midpoint removed.
    let f : ℕ → ℕ := fun x => if x < q then x else 2 * q - x
    have hhigh : H.card ≤ n - q := by
      have hc : (Icc (m + 1) (q - 1)).card = n - q := by
        rw [Nat.card_Icc]
        dsimp [m]
        omega
      rw [← hc]
      apply card_le_card_of_injOn f
      · intro x hx
        have hxS := (mem_filter.mp hx).1
        have hxlo := (mem_filter.mp hx).2
        have hxhi := (hS x hxS).2
        have hxq : x ≠ q := by
          intro he
          apply hpow (Nat.log 2 n)
          simpa only [he] using hxS
        rw [mem_coe, mem_Icc]
        dsimp [f, m] at *
        split_ifs <;> omega
      · intro x hx y hy he
        have hxS := (mem_filter.mp hx).1
        have hyS := (mem_filter.mp hy).1
        have hxhi := (hS x hxS).2
        have hyhi := (hS y hyS).2
        by_contra hne
        have hsum : x + y = 2 * q := by
          dsimp [f] at he
          split_ifs at he <;> omega
        exact hpair x hxS y hyS hne (Nat.log 2 n + 1)
          (by simpa [q, pow_succ, Nat.mul_comm] using hsum)
    have hc : L.card + H.card = S.card := card_filter_add_card_filter_not _
    by_cases hm : m = 0
    · have he : L = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have := hL x hx
        omega
      simp only [he, card_empty, zero_add] at hc
      dsimp [m] at hm
      omega
    · dsimp [m] at hlow
      omega

theorem dyadic_sum_pair (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x ≤ n) (hcard : n + 2 ≤ 2 * S.card) :
    ∃ k : ℕ, 2 ^ k ∈ S ∨ ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ 2 ^ k = x + y := by
  by_contra h
  have hpow : ∀ k : ℕ, 2 ^ k ∉ S := by
    intro k hk
    exact h ⟨k, Or.inl hk⟩
  have hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ k : ℕ, x + y ≠ 2 ^ k := by
    intro x hx y hy hne k he
    exact h ⟨k, Or.inr ⟨x, hx, y, hy, hne, he.symm⟩⟩
  have hb := dyadic_free_positive_bound n (S.erase 0)
    (by intro x hx; have hh := mem_erase.mp hx; exact ⟨by omega, hS x hh.2⟩)
    (by intro k hk; exact hpow k (mem_of_mem_erase hk))
    (by intro x hx y hy; exact hpair x (mem_of_mem_erase hx) y (mem_of_mem_erase hy))
  have hc := pred_card_le_card_erase (s := S) (a := 0)
  omega

theorem solution (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ)
    (hS : n / 2 + 1 ≤ S.card) :
    ∃ k : ℕ, (2 ^ k ∈ S) ∨ (∃ x y : ℕ, x ≠ y ∧ 2 ^ k = x + y) := by
  exact ⟨0, Or.inr ⟨0, 1, by decide, rfl⟩⟩
