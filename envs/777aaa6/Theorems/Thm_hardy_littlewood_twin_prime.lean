-- Prove2me | Theorems.Thm_hardy_littlewood_twin_prime
-- name    : hardy_littlewood_twin_prime
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:59:49.945478+00:00
-- url     : https://prove2.me/theorems/e98c0857-f70f-4515-871b-965e5772fdec
-- statement:
--   Hardy-Littlewood twin prime conjecture (Conjecture B, 1923): The number of twin primes (p, p+2) up to x is asymptotically C₂·x/(log x)², where C₂ ≈ 1.3203 is the twin prime constant. Stronger than the twin prime conjecture; gives quantitative asymptotics.
-- source:
--   https://en.wikipedia.org/wiki/Twin_prime

import Mathlib

import Mathlib

-- Hardy-Littlewood Conjecture B: the number of twin prime pairs (p, p+2) ≤ x
-- is asymptotically C₂ * x / (log x)² where C₂ ≈ 1.3203... is the twin prime constant
theorem hardy_littlewood_twin_prime :
    ∃ C : ℝ, 0 < C ∧
    Filter.Tendsto (fun x : ℝ =>
      ((Finset.Icc 2 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))).card /
      (x / (Real.log x)^2))
    Filter.atTop
    (nhds C) := by
  sorry
