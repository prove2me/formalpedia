-- Prove2me | Theorems.Thm_grimm_conjecture
-- name    : grimm_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:30:25.683214+00:00
-- url     : https://prove2.me/theorems/f58c308f-fa25-4604-b536-9f40519be982
-- statement:
--   **Grimm's Conjecture**: If $n, n+1, \ldots, n+m$ are all composite numbers, then there exist distinct primes $p_0, p_1, \ldots, p_m$ with $p_i \mid n+i$ for each $i$.
--
--   In other words, for any maximal run of consecutive composites, we can assign a distinct prime divisor to each composite.
--
--   Proposed by Carl Albert Grimm in 1969. Verified for $n \leq 10^{11}$ (Alaoglu and Erdős, with later extensions). Implied by the abc conjecture. Known to hold conditionally under Cramér's conjecture on prime gaps.
-- source:
--   https://en.wikipedia.org/wiki/Grimm%27s_conjecture

import Mathlib

theorem grimm_conjecture (n m : ℕ) (hn : 2 ≤ n)
    (hm : 1 ≤ m)
    (hcomp : ∀ k, n ≤ k → k ≤ n + m → ¬Nat.Prime k) :
    ∃ f : Fin (m + 1) → ℕ,
      Function.Injective f ∧
      ∀ i, Nat.Prime (f i) ∧ f i ∣ (n + i) := by
  sorry
