-- Prove2me | solution 1 for lean_workbook_plus_67383
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:57:00.832773+00:00
-- url     : https://prove2.me/submissions/940d5458-5023-45c0-bf11-250129fef1c6

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

def primeSum102Pairs : Finset (ℕ × ℕ) :=
  {(59, 43), (61, 41), (71, 31), (73, 29),
   (79, 23), (83, 19), (89, 13), (97, 5)}

theorem prime_sum_102_classification (p q : ℕ) :
    p.Prime ∧ q.Prime ∧ q < p ∧ p + q = 102 ↔
      (p, q) ∈ primeSum102Pairs := by
  constructor
  · rintro ⟨hp, hq, hpq, hsum⟩
    have hpbound : p ≤ 102 := by omega
    have hqeq : q = 102 - p := by omega
    subst q
    interval_cases p <;> norm_num [primeSum102Pairs] at *
  · intro h
    simp only [primeSum102Pairs, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at h
    rcases h with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;> norm_num

theorem prime_sum_102_minimum :
    IsLeast {d : ℕ | ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ q < p ∧ p + q = 102 ∧ d = p - q} 16 := by
  constructor
  · exact ⟨59, 43, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
  · rintro d ⟨p, q, hp, hq, hpq, hsum, rfl⟩
    have h := (prime_sum_102_classification p q).mp ⟨hp, hq, hpq, hsum⟩
    simp only [primeSum102Pairs, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at h
    rcases h with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;> norm_num

theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p > q) (h : p + q = 102) : p - q ≥ 3 := by
  have hmin := prime_sum_102_minimum.2 ⟨p, q, hp, hq, hpq, h, rfl⟩
  omega
