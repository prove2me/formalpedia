-- Prove2me | Theorems.Thm_hardy_littlewood_conjecture_A
-- name    : hardy_littlewood_conjecture_A
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:02:15.889216+00:00
-- url     : https://prove2.me/theorems/4e260ff2-14da-4fe4-b362-8a8df2ff5cdf
-- statement:
--   **Hardy–Littlewood Conjecture A (First Hardy–Littlewood Conjecture)**: The number of prime pairs $(p, p+2k)$ with $p \leq x$ for any fixed even $k$ is asymptotically
--   $$\pi_2(x, k) \sim 2C_2 \prod_{p \mid k, p > 2} \frac{p-1}{p-2} \cdot \frac{x}{(\ln x)^2}$$
--   where $C_2 = \prod_{p \geq 3} \frac{p(p-2)}{(p-1)^2} \approx 0.6601618$ is the twin prime constant.
--
--   As a theorem, this asserts infinitely many prime pairs $(p, p+2k)$ for every even $k$, which is Polignac's conjecture. As stated here (the parity of density), this generalizes the twin prime conjecture. The asymptotic form is open; even the infinitude is open for any specific $k$.
--
--   **Source**: Hardy, G.H., Littlewood, J.E. (1923). Some problems of 'Partitio Numerorum' III. Acta Math. 44, 1–70. DOI:10.1007/BF02403921
-- source:
--   https://en.wikipedia.org/wiki/Hardy%E2%80%93Littlewood_conjecture

import Mathlib

theorem hardy_littlewood_conjecture_A (k : ℕ) (hk : 0 < k) (hk2 : Even k) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + k)}.Infinite := by
  sorry
