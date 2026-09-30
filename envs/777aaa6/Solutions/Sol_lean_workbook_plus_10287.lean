-- Prove2me | solution 1 for lean_workbook_plus_10287
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:13:23.394438+00:00
-- url     : https://prove2.me/submissions/dff908f9-3ef8-4521-9844-0570ae49ad97

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

theorem bounded_fraction_real_pair_classification (x : ℝ) (k : ℤ) :
    (1 ≤ x ∧ x ≤ 2014 ∧ 8 * x / (9999 - x) = (k : ℝ)) ↔
      (x = 1111 ∧ k = 1) ∨ (x = 9999 / 5 ∧ k = 2) := by
  constructor
  · rintro ⟨hlo, hhi, h⟩
    have hd : 0 < 9999 - x := by linarith
    have hklo : (0 : ℝ) < k := by
      rw [← h]
      exact div_pos (by linarith) hd
    have hkhi : (k : ℝ) < 3 := by
      rw [← h]
      apply (div_lt_iff₀ hd).mpr
      linarith
    have hk : 1 ≤ k ∧ k ≤ 2 := by
      have h0 : (0 : ℤ) < k := by exact_mod_cast hklo
      have h3 : k < (3 : ℤ) := by exact_mod_cast hkhi
      omega
    have hp := (div_eq_iff hd.ne').mp h
    rcases hk with ⟨hklo, hkhi⟩
    interval_cases k
    · left
      norm_num at hp
      exact ⟨by linarith, rfl⟩
    · right
      norm_num at hp
      exact ⟨by linarith, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem bounded_fraction_real_classification (x : ℝ) :
    (1 ≤ x ∧ x ≤ 2014 ∧ ∃ k : ℤ, 8 * x / (9999 - x) = (k : ℝ)) ↔
      x = 1111 ∨ x = 9999 / 5 := by
  constructor
  · rintro ⟨hlo, hhi, k, h⟩
    rcases (bounded_fraction_real_pair_classification x k).mp ⟨hlo, hhi, h⟩ with
      ⟨hx, _⟩ | ⟨hx, _⟩
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, by norm_num, 1, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, 2, by norm_num⟩

theorem bounded_fraction_real_count :
    Nat.card {x : ℝ // 1 ≤ x ∧ x ≤ 2014 ∧
      ∃ k : ℤ, 8 * x / (9999 - x) = (k : ℝ)} = 2 := by
  classical
  let e : {x : ℝ // 1 ≤ x ∧ x ≤ 2014 ∧
      ∃ k : ℤ, 8 * x / (9999 - x) = (k : ℝ)} ≃
      ({1111, 9999 / 5} : Finset ℝ) :=
    Equiv.subtypeEquivRight (fun x => by
      simpa using bounded_fraction_real_classification x)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  norm_num

theorem bounded_fraction_integer_pair_classification (n k : ℤ) :
    (1 ≤ n ∧ n ≤ 2014 ∧ 8 * n = k * (9999 - n)) ↔ n = 1111 ∧ k = 1 := by
  constructor
  · rintro ⟨hlo, hhi, h⟩
    have hlor : (1 : ℝ) ≤ n := by exact_mod_cast hlo
    have hhir : (n : ℝ) ≤ 2014 := by exact_mod_cast hhi
    have hd : (9999 : ℝ) - n ≠ 0 := by linarith
    have hr : 8 * (n : ℝ) = (k : ℝ) * (9999 - n) := by exact_mod_cast h
    have hh := (bounded_fraction_real_pair_classification n k).mp
      ⟨hlor, hhir, (div_eq_iff hd).mpr hr⟩
    rcases hh with ⟨hn, hk⟩ | ⟨hn, _⟩
    · exact ⟨by exact_mod_cast hn, hk⟩
    · have hn5 : (5 : ℝ) * n = 9999 := by rw [hn]; norm_num
      have hn5z : (5 : ℤ) * n = 9999 := by exact_mod_cast hn5
      omega
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem bounded_fraction_integer_classification (n : ℤ) :
    (1 ≤ n ∧ n ≤ 2014 ∧ ∃ k : ℤ, 8 * n = k * (9999 - n)) ↔ n = 1111 := by
  constructor
  · rintro ⟨hlo, hhi, k, h⟩
    exact ((bounded_fraction_integer_pair_classification n k).mp ⟨hlo, hhi, h⟩).1
  · rintro rfl
    exact ⟨by norm_num, by norm_num, 1, by norm_num⟩

theorem bounded_fraction_integer_count :
    Nat.card {n : ℤ // 1 ≤ n ∧ n ≤ 2014 ∧
      ∃ k : ℤ, 8 * n = k * (9999 - n)} = 1 := by
  let e : {n : ℤ // 1 ≤ n ∧ n ≤ 2014 ∧
      ∃ k : ℤ, 8 * n = k * (9999 - n)} ≃ ({1111} : Finset ℤ) :=
    Equiv.subtypeEquivRight (fun n => by
      simpa using bounded_fraction_integer_classification n)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  norm_num

theorem solution : ∃ n, (1 ≤ n ∧ n ≤ 2014 ∧ ∃ k : ℤ, 8 * n = k * (9999 - n)) := by
  exact ⟨1111, (bounded_fraction_integer_classification 1111).mpr rfl⟩
