-- Prove2me | Theorems.Thm_e_normality_conjecture
-- name    : e_normality_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:32:25.010133+00:00
-- url     : https://prove2.me/theorems/1df9844e-7331-4874-a9e7-c25f3a9ed41f
-- statement:
--   Normality of e: Each digit d appears with frequency 1/b in the base-b expansion of e. Unproved for any specific digit in any base.
-- source:
--   https://en.wikipedia.org/wiki/Normal_number

import Mathlib

import Mathlib

theorem e_normality_conjecture (b : ℕ) (hb : 2 ≤ b) (d : ℕ) (hd : d < b) :
    Filter.Tendsto (fun n : ℕ =>
      ((Finset.range n).filter (fun k =>
        Nat.floor (Real.exp 1 * (b : ℝ) ^ k) % b = d)).card / (n : ℝ))
    Filter.atTop (nhds (1 / b)) := by
  sorry
