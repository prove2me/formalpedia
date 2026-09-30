-- Prove2me | solution 1 for lean_workbook_plus_65698
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:31:44.870908+00:00
-- url     : https://prove2.me/submissions/5527cec7-2e1f-45e4-a438-cdf9dbc13c5b

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

private theorem composite_progression (k : ℕ) :
    ¬ Nat.Prime (6 * (77 * k + 20) - 1) ∧
      ¬ Nat.Prime (6 * (77 * k + 20) + 1) := by
  have hleft : 6 * (77 * k + 20) - 1 = 7 * (66 * k + 17) := by omega
  have hright : 6 * (77 * k + 20) + 1 = 11 * (42 * k + 11) := by omega
  constructor
  · intro hp
    have hdiv : 7 ∣ 6 * (77 * k + 20) - 1 := ⟨66 * k + 17, hleft⟩
    have := (Nat.dvd_prime hp).mp hdiv
    omega
  · intro hp
    have hdiv : 11 ∣ 6 * (77 * k + 20) + 1 := ⟨42 * k + 11, hright⟩
    have := (Nat.dvd_prime hp).mp hdiv
    omega

private theorem arbitrarily_large_composites (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ¬ Nat.Prime (6 * n - 1) ∧ ¬ Nat.Prime (6 * n + 1) := by
  exact ⟨77 * B + 20, by omega, composite_progression B⟩

theorem solution : ∃ n, ¬ Nat.Prime (6 * n - 1) ∧ ¬ Nat.Prime (6 * n + 1) := by
  obtain ⟨n, _, hn⟩ := arbitrarily_large_composites 0
  exact ⟨n, hn⟩
