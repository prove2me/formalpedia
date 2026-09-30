-- Prove2me | solution 1 for lean_workbook_plus_14481
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:10:08.823935+00:00
-- url     : https://prove2.me/submissions/671d7b37-17d1-44b0-8768-5cfb17ec9583

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution (n : ℕ) : ¬ 2 ∣ n^2 + n + 1 := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;>
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h]
