-- Prove2me | solution 2 for Singmaster.mult_24310
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T19:18:32.721539+00:00
-- url     : https://prove2.me/submissions/afa39849-869f-4126-bb4f-bb8ac1969e06

import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterOccurrences

open Finset Singmaster in
theorem solution : mult 24310 = 6 := by
  classical
  -- unimodality on the left half of a row
  have huni : ∀ n a b : ℕ, a ≤ b → b ≤ n / 2 → n.choose a ≤ n.choose b := by
    intro n a b hab hb
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih =>
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  -- strict growth down a column
  have hcol : ∀ a k : ℕ, 1 ≤ k → k ≤ a → a.choose k < (a + 1).choose k := by
    intro a k hk hka
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.choose_succ_succ']
    have : 0 < a.choose j := Nat.choose_pos (by omega)
    omega
  have hcolmono : ∀ a b k : ℕ, 1 ≤ k → k ≤ a → a + 1 ≤ b → a.choose k < b.choose k := by
    intro a b k hk hka hab
    induction b, hab using Nat.le_induction with
    | base => exact hcol a k hk hka
    | succ b hb ih => exact ih.trans (hcol b k hk (by omega))
  -- a strict gap between consecutive rows excludes a column
  have hgap : ∀ j g n : ℕ, g.descFactorial j < j.factorial * 24310 →
      j.factorial * 24310 < (g + 1).descFactorial j → n.choose j ≠ 24310 := by
    intro j g n hlo hhi hc
    rcases le_or_gt n g with hle | hgt
    · have h1 : n.choose j ≤ g.choose j := Nat.choose_le_choose j hle
      have h2 := Nat.descFactorial_eq_factorial_mul_choose g j
      rw [hc] at h1
      have h3 : j.factorial * 24310 ≤ j.factorial * g.choose j := Nat.mul_le_mul_left _ h1
      omega
    · have h1 : (g + 1).choose j ≤ n.choose j := Nat.choose_le_choose j hgt
      have h2 := Nat.descFactorial_eq_factorial_mul_choose (g + 1) j
      rw [hc] at h1
      have h3 : j.factorial * (g + 1).choose j ≤ j.factorial * 24310 := Nat.mul_le_mul_left _ h1
      omega
  -- an exact hit between two strict gaps pins down the row
  have hexact : ∀ j n0 n : ℕ, 1 ≤ n0 → (n0 - 1).descFactorial j < j.factorial * 24310 →
      j.factorial * 24310 < (n0 + 1).descFactorial j → n.choose j = 24310 → n = n0 := by
    intro j n0 n hn0 hlo hhi hc
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : n.choose j ≤ (n0 - 1).choose j := Nat.choose_le_choose j (by omega)
      have h2 := Nat.descFactorial_eq_factorial_mul_choose (n0 - 1) j
      rw [hc] at h1
      have h3 : j.factorial * 24310 ≤ j.factorial * (n0 - 1).choose j := Nat.mul_le_mul_left _ h1
      omega
    · have h1 : (n0 + 1).choose j ≤ n.choose j := Nat.choose_le_choose j hgt
      have h2 := Nat.descFactorial_eq_factorial_mul_choose (n0 + 1) j
      rw [hc] at h1
      have h3 : j.factorial * (n0 + 1).choose j ≤ j.factorial * 24310 := Nat.mul_le_mul_left _ h1
      omega
  have hocc : occ 24310 = {(24310, 1), (24310, 24309), (221, 2), (221, 219), (17, 8), (17, 9)} := by
    ext ⟨n, k⟩
    simp only [occ, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hn, hk⟩, hkn, hc⟩
      obtain ⟨j, hjdef⟩ : ∃ j, j = min k (n - k) := ⟨_, rfl⟩
      have hjc : n.choose j = 24310 := by
        rcases le_total k (n - k) with h | h
        · rw [hjdef, min_eq_left h]
          exact hc
        · rw [hjdef, min_eq_right h, Nat.choose_symm hkn]
          exact hc
      have hjhalf : j ≤ n / 2 := by
        rw [hjdef]
        omega
      have hjk : j = k ∨ j = n - k := by
        rw [hjdef]
        omega
      rcases Nat.lt_or_ge j 9 with hj9 | hj9
      · interval_cases j
        · rw [Nat.choose_zero_right] at hjc
          omega
        · rw [Nat.choose_one_right] at hjc
          omega
        · have := hexact 2 221 n (by norm_num) (by decide +kernel) (by decide +kernel) hjc
          omega
        · exact absurd hjc (hgap 3 53 n (by decide +kernel) (by decide +kernel))
        · exact absurd hjc (hgap 4 29 n (by decide +kernel) (by decide +kernel))
        · exact absurd hjc (hgap 5 21 n (by decide +kernel) (by decide +kernel))
        · exact absurd hjc (hgap 6 18 n (by decide +kernel) (by decide +kernel))
        · exact absurd hjc (hgap 7 17 n (by decide +kernel) (by decide +kernel))
        · have := hexact 8 17 n (by norm_num) (by decide +kernel) (by decide +kernel) hjc
          omega
      · exfalso
        have h1 : (2 * j).choose j ≤ n.choose j := Nat.choose_le_choose j (by omega)
        have h2 : (18 : ℕ).choose 9 ≤ (2 * j).choose 9 := Nat.choose_le_choose 9 (by omega)
        have h3 : (2 * j).choose 9 ≤ (2 * j).choose (2 * j / 2) := Nat.choose_le_middle 9 (2 * j)
        rw [show 2 * j / 2 = j by omega] at h3
        have h4 : (18 : ℕ).choose 9 = 48620 := by
          rw [Nat.choose_eq_descFactorial_div_factorial]
          decide +kernel
        omega
    · have e221 : (221 : ℕ).choose 2 = 24310 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      have e17 : (17 : ℕ).choose 8 = 24310 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num, Nat.choose_one_right _⟩
      · refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
        rw [show (24309 : ℕ) = 24310 - 1 by norm_num, Nat.choose_symm (by norm_num),
          Nat.choose_one_right]
      · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num, e221⟩
      · refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
        rw [show (219 : ℕ) = 221 - 2 by norm_num, Nat.choose_symm (by norm_num)]
        exact e221
      · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num, e17⟩
      · refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
        rw [show (9 : ℕ) = 17 - 8 by norm_num, Nat.choose_symm (by norm_num)]
        exact e17
  unfold mult
  rw [hocc]
  decide
