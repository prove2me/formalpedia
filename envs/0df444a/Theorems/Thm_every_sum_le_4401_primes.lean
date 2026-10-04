-- Prove2me | Theorems.Thm_every_sum_le_4401_primes
-- name    : every_sum_le_4401_primes
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:23:05.703201+00:00
-- url     : https://prove2.me/theorems/bdf56966-0fdb-4d7b-bfa6-6b7f9c4af81a
-- title:
--   Schnirelmann's theorem: every integer greater than 1 is a sum of at most 4401 primes
-- statement:
--   Every integer greater than $1$ — even or odd — is a sum of at most $4401$ primes.
--
--   $$\forall\ n > 1,\quad \exists\ \text{primes } p_1, \dots, p_k,\ k \le 4401,\quad n = p_1 + \dots + p_k.$$
--
--   This is Schnirelmann's 1932 theorem in its historical form: there exists a constant $K$ such that every integer greater than $1$ is a sum of at most $K$ primes. It was the first unconditional approximation to Goldbach's conjecture ever proved, and its method — positive Schnirelmann density of the two-prime sumset, combined with an iteration for sumset densities — created additive number theory. Here the statement is instantiated with the platform's current best constant $K = 4401$ from the odd-Goldbach campaign: strictly stronger than the campaign entry `odd_sum_le_4401_primes` (which is restricted to odd $n$), because even $n$ are covered too — a single $2$ plus $4400$ odd primes for $n \ge 13202$, and explicit padding with $3$s and $2$s below that.
--
--   **Formalization Note** The primes form a `Multiset ℕ`. The proof combines the platform theorems `Schnir.density_A_2200` and `Schnirelmann.mann` exactly as in `odd_sum_le_4401_primes`; the even cases reuse the same `4400$-odd-prime decomposition with a leading $2$.
-- source:
--   L. Schnirelmann, Uber additive Eigenschaften von Zahlen, Math. Ann. 107 (1932), 649-690 (existence of a finite K such that every integer > 1 is a sum of at most K primes); explicit K = 4401 via the odd-Goldbach campaign machinery (Schnirelmann.mann, Schnir.density_A_2200)

import Mathlib

theorem every_sum_le_4401_primes (n : ℕ) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 4401 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by sorry
