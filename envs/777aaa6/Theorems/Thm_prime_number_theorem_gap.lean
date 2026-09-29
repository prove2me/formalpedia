-- Prove2me | Theorems.Thm_prime_number_theorem_gap
-- name    : prime_number_theorem_gap
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:45:02.363112+00:00
-- url     : https://prove2.me/theorems/1952717c-6a87-4464-9d85-e852c175f6f6
-- statement:
--   Prime number theorem: π(x) ~ x/log x. Proved by Hadamard and de la Vallée Poussin (1896). Li(x) approximation is much better. Error term O(x exp(-c√log x)) is known; RH implies O(x^{1/2} log x).
-- source:
--   https://en.wikipedia.org/wiki/Prime_number_theorem

import Mathlib

import Mathlib

theorem prime_number_theorem_gap :
    Filter.Tendsto (fun x : ℝ =>
      (∑ p ∈ (Finset.range (Nat.floor x)).filter Nat.Prime, (1 : ℝ)) /
      (x / Real.log x))
    Filter.atTop (nhds 1) := by
  sorry
