-- Prove2me | Theorems.Thm_pi_normality_conjecture
-- name    : pi_normality_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:32:13.85002+00:00
-- url     : https://prove2.me/theorems/99f45873-6b28-4041-9f96-eb1b270555d3
-- statement:
--   Normality of π: Each digit d appears with frequency 1/b in base b. No digit of π has been proved to appear with frequency ≠ 1/b. Almost certainly true but utterly unproved.
-- source:
--   https://en.wikipedia.org/wiki/Normal_number

import Mathlib

import Mathlib

theorem pi_normality_conjecture (b : ℕ) (hb : 2 ≤ b) (d : ℕ) (hd : d < b) :
    Filter.Tendsto (fun n : ℕ =>
      ((Finset.range n).filter (fun k =>
        Nat.floor (Real.pi * (b : ℝ) ^ k) % b = d)).card / (n : ℝ))
    Filter.atTop (nhds (1 / b)) := by
  sorry
