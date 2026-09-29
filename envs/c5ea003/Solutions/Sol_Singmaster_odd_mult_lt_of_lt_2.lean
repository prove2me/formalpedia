-- Prove2me | solution 2 for Singmaster.odd_mult_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T19:12:48.207986+00:00
-- url     : https://prove2.me/submissions/1e06b686-a073-422a-8749-149e49011544

import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterOccurrences

open Finset Singmaster in
theorem solution {t : ℕ} (ht : 2 ≤ t) (hlt : t < 705432)
    (hodd : Odd (mult t)) : mult t = 1 ∨ mult t = 3 := by
  classical
  have main20 : ∀ m : ℕ, 2 ≤ m → m ≤ 10 → mult ((2 * m).choose m) = 3 := by
    intro m hm hm'
    have crit : ∀ (m t s : ℕ) (g : ℕ → ℕ), 3 ≤ m → (2 * m).choose m = t →
        s * s < 8 * t + 1 → 8 * t + 1 < (s + 1) * (s + 1) →
        (∀ k ∈ Finset.Icc 3 (m - 1), (g k).descFactorial k < k.factorial * t ∧
          k.factorial * t < (g k + 1).descFactorial k) →
        mult t = 3 := by
      intro m t s g hm hval hs1 hs2 hg
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
      have ht15 : 15 ≤ t := by
        have : 3 * 5 ≤ m * (2 * m - 1) := Nat.mul_le_mul hm (by omega)
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
          rcases Nat.lt_or_ge j 3 with hj3 | hj3
          · interval_cases j
            · rw [Nat.choose_zero_right] at hjc
              omega
            · rw [Nat.choose_one_right] at hjc
              omega
            · -- `C(n,2) = t` would make `8t + 1` a perfect square
              exfalso
              have hn4 : 4 ≤ n := by omega
              have h2t : 2 * t = n * (n - 1) := by
                rw [← hjc, Nat.choose_two_right]
                exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
              have hu : 8 * t + 1 = (2 * n - 1) * (2 * n - 1) := by
                rw [hsq n (by omega)]
                omega
              rw [hu] at hs1 hs2
              have e1 := Nat.mul_self_lt_mul_self_iff.1 hs1
              have e2 := Nat.mul_self_lt_mul_self_iff.1 hs2
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
              · obtain ⟨hlo, hhi⟩ := hg j (Finset.mem_Icc.2 ⟨hj3, by omega⟩)
                rcases le_or_gt n (g j) with hle | hgt'
                · have h1 : n.choose j ≤ (g j).choose j := Nat.choose_le_choose j hle
                  have h2 := Nat.descFactorial_eq_factorial_mul_choose (g j) j
                  rw [hjc] at h1
                  have h3 : j.factorial * t ≤ j.factorial * (g j).choose j := Nat.mul_le_mul_left _ h1
                  omega
                · have h1 : (g j + 1).choose j ≤ n.choose j := Nat.choose_le_choose j hgt'
                  have h2 := Nat.descFactorial_eq_factorial_mul_choose (g j + 1) j
                  rw [hjc] at h1
                  have h3 : j.factorial * (g j + 1).choose j ≤ j.factorial * t :=
                    Nat.mul_le_mul_left _ h1
                  omega
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
    interval_cases m
    · decide +kernel
    · have hv : (2 * 3).choose 3 = 20 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      rw [hv]
      exact crit 3 20 12 (fun k => ([] : List ℕ).getD (k - 3) 0) (by norm_num) hv
        (by norm_num) (by norm_num) (by decide +kernel)
    · have hv : (2 * 4).choose 4 = 70 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      rw [hv]
      exact crit 4 70 23 (fun k => [8].getD (k - 3) 0) (by norm_num) hv
        (by norm_num) (by norm_num) (by decide +kernel)
    · have hv : (2 * 5).choose 5 = 252 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      rw [hv]
      exact crit 5 252 44 (fun k => [12, 10].getD (k - 3) 0) (by norm_num) hv
        (by norm_num) (by norm_num) (by decide +kernel)
    · have hv : (2 * 6).choose 6 = 924 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      rw [hv]
      exact crit 6 924 85 (fun k => [18, 13, 12].getD (k - 3) 0) (by norm_num) hv
        (by norm_num) (by norm_num) (by decide +kernel)
    · have hv : (2 * 7).choose 7 = 3432 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      rw [hv]
      exact crit 7 3432 165 (fun k => [28, 18, 15, 14].getD (k - 3) 0) (by norm_num) hv
        (by norm_num) (by norm_num) (by decide +kernel)
    · have hv : (2 * 8).choose 8 = 12870 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      rw [hv]
      exact crit 8 12870 320 (fun k => [43, 25, 19, 17, 16].getD (k - 3) 0) (by norm_num) hv
        (by norm_num) (by norm_num) (by decide +kernel)
    · have hv : (2 * 9).choose 9 = 48620 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      rw [hv]
      exact crit 9 48620 623 (fun k => [67, 34, 24, 20, 18, 18].getD (k - 3) 0) (by norm_num) hv
        (by norm_num) (by norm_num) (by decide +kernel)
    · have hv : (2 * 10).choose 10 = 184756 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        decide +kernel
      rw [hv]
      exact crit 10 184756 1215 (fun k => [104, 47, 31, 25, 22, 20, 20].getD (k - 3) 0) (by norm_num) hv
        (by norm_num) (by norm_num) (by decide +kernel)
  -- odd multiplicity forces a central occurrence
  have hpair : ∃ k, (2 * k).choose k = t ∧ 2 * k ≤ t := by
    by_contra hno
    have hno' : ∀ k, (2 * k).choose k = t → t < 2 * k := by
      intro k hk
      by_contra h
      exact hno ⟨k, hk, by omega⟩
    have hmem : ∀ p : ℕ × ℕ, p ∈ occ t ↔
        p.1 < t + 1 ∧ p.2 < t + 1 ∧ p.2 ≤ p.1 ∧ p.1.choose p.2 = t := by
      intro p
      simp only [occ, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      tauto
    have hsplit : occ t = (occ t).filter (fun p => 2 * p.2 < p.1)
        ∪ (occ t).filter (fun p => p.1 < 2 * p.2) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hp
        have hne : p.1 ≠ 2 * p.2 := by
          intro h
          have h1 := (hmem p).1 hp
          have h2 := hno' p.2 (by rw [← h]; exact h1.2.2.2)
          omega
        rcases lt_or_gt_of_ne hne with h | h
        · right
          exact ⟨hp, h⟩
        · left
          exact ⟨hp, h⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    have hdisj : Disjoint ((occ t).filter (fun p => 2 * p.2 < p.1))
        ((occ t).filter (fun p => p.1 < 2 * p.2)) := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega
    have hLR : ((occ t).filter (fun p => 2 * p.2 < p.1)).card
        = ((occ t).filter (fun p => p.1 < 2 * p.2)).card := by
      apply Finset.card_bij (fun p _ => (p.1, p.1 - p.2))
      · intro p hp
        rw [Finset.mem_filter] at hp ⊢
        have h1 := (hmem p).1 hp.1
        refine ⟨(hmem _).2 ⟨h1.1, by simp only; omega, by simp only; omega, ?_⟩, by simp only; omega⟩
        simp only
        rw [Nat.choose_symm h1.2.2.1]
        exact h1.2.2.2
      · intro p hp q hq h
        rw [Finset.mem_filter] at hp hq
        have h1 := (hmem p).1 hp.1
        have h2 := (hmem q).1 hq.1
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (by omega)
      · intro b hb
        rw [Finset.mem_filter] at hb
        have h1 := (hmem b).1 hb.1
        refine ⟨(b.1, b.1 - b.2), ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨(hmem _).2 ⟨h1.1, by simp only; omega, by simp only; omega, ?_⟩, by simp only; omega⟩
          simp only
          rw [Nat.choose_symm h1.2.2.1]
          exact h1.2.2.2
        · exact Prod.ext rfl (show b.1 - (b.1 - b.2) = b.2 by omega)
    have heven : Even (mult t) := by
      unfold mult
      rw [hsplit, Finset.card_union_of_disjoint hdisj, hLR]
      exact ⟨_, rfl⟩
    exact (Nat.not_even_iff_odd.2 hodd) heven
  obtain ⟨k, hk, hk2⟩ := hpair
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk
      omega
    · omega
  have hk20 : k ≤ 10 := by
    by_contra h
    have h42 : (22 : ℕ).choose 11 = 705432 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide +kernel
    have e1 : (22 : ℕ).choose 11 ≤ (2 * k).choose 11 := Nat.choose_le_choose 11 (by omega)
    have e2 : (2 * k).choose 11 ≤ (2 * k).choose (2 * k / 2) := Nat.choose_le_middle 11 (2 * k)
    rw [show 2 * k / 2 = k by omega, hk] at e2
    omega
  rcases Nat.lt_or_ge k 2 with hkl | hkg
  · left
    have hk' : k = 1 := by omega
    subst hk'
    rw [← hk]
    decide +kernel
  · right
    rw [← hk]
    exact main20 k hkg hk20
