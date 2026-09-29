-- Prove2me | Theorems.Thm_kurepa_conjecture
-- name    : kurepa_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:54:08.206525+00:00
-- url     : https://prove2.me/theorems/1018db3b-5708-4f1f-a11d-7b2c33a05ea7
-- statement:
--   Stub - kurepa_conjecture
-- source:
--   https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics

import Mathlib

theorem kurepa_conjecture (p : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) :
    ¬ (p : ℤ) ∣ ∑ j ∈ Finset.range p, (Nat.factorial j : ℤ) := by
  sorry
