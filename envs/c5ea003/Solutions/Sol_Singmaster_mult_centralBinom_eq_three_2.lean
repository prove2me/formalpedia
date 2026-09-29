-- Prove2me | solution 2 for Singmaster.mult_centralBinom_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T02:10:11.249748+00:00
-- url     : https://prove2.me/submissions/246f2a5e-b576-40dd-9cf2-78ea4f595938

import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterOccurrences

open Finset Singmaster in
theorem solution {m N : ℕ} (hm : 2 ≤ m) (hN2 : 2 ≤ N)
    (hN : (2 * m).choose m < N.choose 2) (H : NoInteriorRepeat m N) :
    mult ((2 * m).choose m) = 3 := by
  classical
  obtain ⟨t, hval⟩ : ∃ t, (2 * m).choose m = t := ⟨_, rfl⟩
  have HN : ∀ n, 2 * m + 1 ≤ n → n < N → ∀ k, 2 ≤ k → k ≤ n / 2 →
      n.descFactorial k ≠ Nat.factorial k * t := by
    intro n hn1 hn2 k hk1 hk2
    rw [← hval]
    exact H n (Finset.mem_Ico.2 ⟨hn1, hn2⟩) k (Finset.mem_Icc.2 ⟨hk1, hk2⟩)
  rw [hval] at hN ⊢
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
  -- size of `t`
  have hC2 : (2 * m).choose 2 = m * (2 * m - 1) := by
    rw [Nat.choose_two_right]
    have e : 2 * m * (2 * m - 1) = 2 * (m * (2 * m - 1)) := by ring
    rw [e, Nat.mul_div_cancel_left _ (by norm_num)]
  have ht2 : m * (2 * m - 1) ≤ t := by
    have h := huni (2 * m) 2 m (by omega) (by omega)
    rw [hC2, hval] at h
    exact h
  have hm3 : m * 3 ≤ m * (2 * m - 1) := Nat.mul_le_mul_left m (by omega)
  have ht15 : 6 ≤ t := by
    have : 2 * 3 ≤ m * (2 * m - 1) := Nat.mul_le_mul hm (by omega)
    omega
  have h2mt : 2 * m < t := by omega
  -- `(2n − 1)² = 4 n (n − 1) + 1`
  have hsq : ∀ n : ℕ, 1 ≤ n → (2 * n - 1) * (2 * n - 1) = 4 * (n * (n - 1)) + 1 := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (p + 1) - 1 = 2 * p + 1 by omega, show p + 1 - 1 = p by omega]
    ring
  -- `C(2m, m) = C(2m−1, m−1) + C(2m−1, m)`
  have hsplit : (2 * m).choose m = (2 * m - 1).choose (m - 1) + (2 * m - 1).choose m := by
    have e := Nat.choose_succ_succ' (2 * m - 1) (m - 1)
    rw [show 2 * m - 1 + 1 = 2 * m by omega, show m - 1 + 1 = m by omega] at e
    exact e
  -- `C(2m, m−1) < C(2m, m)`
  have hmid : (2 * m).choose (m - 1) < (2 * m).choose m := by
    have e := Nat.choose_succ_right_eq (2 * m) (m - 1)
    rw [show m - 1 + 1 = m by omega, show 2 * m - (m - 1) = m + 1 by omega] at e
    have hpos : 0 < (2 * m).choose (m - 1) := Nat.choose_pos (by omega)
    have h1 : (2 * m).choose (m - 1) * m < (2 * m).choose m * m := by
      rw [e]
      nlinarith
    exact Nat.lt_of_mul_lt_mul_right h1
  have hocc : occ t = {(t, 1), (t, t - 1), (2 * m, m)} := by
    ext ⟨n, k⟩
    simp only [occ, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hn, hk⟩, hkn, hc⟩
      obtain ⟨j, hjdef⟩ : ∃ j, j = min k (n - k) := ⟨_, rfl⟩
      have hjc : n.choose j = t := by
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
      rcases Nat.lt_or_ge j 2 with hj3 | hj3
      · interval_cases j
        · rw [Nat.choose_zero_right] at hjc
          omega
        · rw [Nat.choose_one_right] at hjc
          omega
      · rcases Nat.lt_trichotomy n (2 * m) with hlt | heq | hgt
        · -- rows above the centre are too small
          exfalso
          have h1 : n.choose j ≤ (2 * m - 1).choose j := Nat.choose_le_choose j (by omega)
          have h2 : (2 * m - 1).choose j ≤ (2 * m - 1).choose ((2 * m - 1) / 2) :=
            Nat.choose_le_middle j (2 * m - 1)
          rw [show (2 * m - 1) / 2 = m - 1 by omega] at h2
          have h3 : 0 < (2 * m - 1).choose m := Nat.choose_pos (by omega)
          omega
        · -- the centre row: only the middle entry
          subst heq
          rcases Nat.lt_or_ge j m with hjm | hjm
          · exfalso
            have h1 := huni (2 * m) j (m - 1) (by omega) (by omega)
            omega
          · have hjm' : j = m := by omega
            right
            right
            refine ⟨rfl, ?_⟩
            omega
        · -- rows below the centre
          exfalso
          rcases Nat.lt_or_ge j m with hjm | hjm
          · have hnN : n < N := by
              by_contra hge
              have h1 : N.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 (by omega)
              have h2 : n.choose 2 ≤ n.choose j := huni n 2 j hj3 hjhalf
              omega
            have hfac := Nat.descFactorial_eq_factorial_mul_choose n j
            rw [hjc] at hfac
            exact HN n (by omega) hnN j hj3 hjhalf hfac
          · have h1 : n.choose m ≤ n.choose j := huni n m j hjm hjhalf
            have h2 : (2 * m).choose m < n.choose m := hcolmono (2 * m) n m (by omega) (by omega) hgt
            omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨by omega, by omega⟩, by omega, Nat.choose_one_right _⟩
      · refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
        rw [Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]
      · exact ⟨⟨by omega, by omega⟩, by omega, hval⟩
  have h1 : ((t, 1) : ℕ × ℕ) ∉ ({(t, t - 1), (2 * m, m)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
    omega
  have h2 : ((t, t - 1) : ℕ × ℕ) ≠ (2 * m, m) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  unfold mult
  rw [hocc, Finset.card_insert_of_notMem h1, Finset.card_pair h2]
