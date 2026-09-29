-- Prove2me | Theorems.Thm_cousin_prime_conjecture
-- name    : cousin_prime_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:08:02.072802+00:00
-- url     : https://prove2.me/theorems/41e43f9d-ec58-4d9c-a3da-e66a6b3a67a8
-- statement:
--   **Cousin Prime Conjecture**: There are infinitely many cousin primes, i.e., prime pairs $(p, p+4)$.
--
--   Examples: $(3, 7)$, $(7, 11)$, $(13, 17)$, $(37, 41)$, $(67, 71)$, $\ldots$ This is a special case of Polignac's conjecture ($k=4$) and Hardy–Littlewood Conjecture A. The heuristic density of cousin primes below $x$ is asymptotically $\sim 2C_2 x / (\ln x)^2$ where $C_2 \approx 0.6602$ is the twin prime constant.
--
--   **Source**: Hardy, G.H., Littlewood, J.E. (1923). Acta Math. 44, 1–70.
-- source:
--   https://en.wikipedia.org/wiki/Cousin_prime

import Mathlib

theorem cousin_prime_conjecture :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 4)}.Infinite := by
  sorry
