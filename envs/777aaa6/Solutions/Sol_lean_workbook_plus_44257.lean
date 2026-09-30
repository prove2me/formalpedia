-- Prove2me | solution 1 for lean_workbook_plus_44257
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:28:04.184216+00:00
-- url     : https://prove2.me/submissions/3ba7a853-cea0-4cdd-85b0-2346e79f82e6

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

def padovanResidue : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 0
  | 6 => 1
  | 7 => 3
  | 8 => 1
  | 9 => 0
  | 10 => 0
  | 11 => 1
  | 12 => 0
  | _ => 1

private theorem padovan_residue_step (n : ℕ) :
    padovanResidue ((n + 3) % 14) =
      (padovanResidue ((n + 1) % 14) + padovanResidue (n % 14)) % 4 := by
  have hn := Nat.mod_lt n (by decide : 0 < 14)
  interval_cases h : n % 14 <;> norm_num [Nat.add_mod, h, padovanResidue]

theorem padovan_mod_four (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 1)
    (a3 : a 2 = 2) (arec : ∀ n, a (n + 3) = a (n + 1) + a n) (n : ℕ) :
    a n % 4 = padovanResidue (n % 14) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | (_ | (_ | n))
      · simpa [padovanResidue] using congrArg (fun k => k % 4) a1
      · simpa [padovanResidue] using congrArg (fun k => k % 4) a2
      · simpa [padovanResidue] using congrArg (fun k => k % 4) a3
      · change a (n + 3) % 4 = padovanResidue ((n + 3) % 14)
        rw [arec, Nat.add_mod, ih (n + 1) (by omega), ih n (by omega)]
        exact (padovan_residue_step n).symm

theorem padovan_period_iff (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 1)
    (a3 : a 2 = 2) (arec : ∀ n, a (n + 3) = a (n + 1) + a n) (k : ℕ) :
    (∀ n, a (n + k) % 4 = a n % 4) ↔ 14 ∣ k := by
  constructor
  · intro hperiod
    have h0 := hperiod 0
    have h1 := hperiod 1
    have h2 := hperiod 2
    simp only [padovan_mod_four a a1 a2 a3 arec] at h0 h1 h2
    have hk := Nat.mod_lt k (by decide : 0 < 14)
    apply Nat.dvd_of_mod_eq_zero
    interval_cases h : k % 14 <;>
      simp_all [Nat.add_mod, padovanResidue]
  · intro hk n
    rw [padovan_mod_four a a1 a2 a3 arec, padovan_mod_four a a1 a2 a3 arec,
      Nat.add_mod, Nat.mod_eq_zero_of_dvd hk, Nat.add_zero, Nat.mod_mod]

theorem padovan_least_period (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 1)
    (a3 : a 2 = 2) (arec : ∀ n, a (n + 3) = a (n + 1) + a n) :
    IsLeast {k : ℕ | 0 < k ∧ ∀ n, a (n + k) % 4 = a n % 4} 14 := by
  refine ⟨⟨by decide, (padovan_period_iff a a1 a2 a3 arec 14).mpr (dvd_refl _)⟩, ?_⟩
  intro k hk
  exact Nat.le_of_dvd hk.1 ((padovan_period_iff a a1 a2 a3 arec k).mp hk.2)

def padovanSequence : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n + 3 => padovanSequence (n + 1) + padovanSequence n

theorem padovan_positive (n : ℕ) : 0 < padovanSequence n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | (_ | (_ | n))
      · decide
      · decide
      · decide
      · exact Nat.add_pos_left (ih (n + 1) (by omega)) _

theorem solution : ¬ (∀ a : ℕ → ℕ, a 0 = 1 → a 1 = 1 → a 2 = 2 →
    (∀ n, a (n + 3) = a (n + 1) + a n) →
    ∀ n, (n ≥ 4 ∧ Even n → a n ≡ 1 [ZMOD 4]) ∧
      (n ≥ 5 ∧ Odd n → a n ≡ 0 [ZMOD 4])) := by
  intro h
  have hbad := (h padovanSequence rfl rfl rfl (fun _ => rfl) 4).1
    ⟨le_rfl, by decide⟩
  have hnat : padovanSequence 4 % 4 = 1 := by
    change (padovanSequence 4 : ℤ) % 4 = 1 at hbad
    exact_mod_cast hbad
  have htable := padovan_mod_four padovanSequence rfl rfl rfl (fun _ => rfl) 4
  change padovanSequence 4 % 4 = 3 at htable
  omega
