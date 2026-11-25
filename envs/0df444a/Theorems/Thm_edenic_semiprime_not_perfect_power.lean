-- Prove2me | Theorems.Thm_edenic_semiprime_not_perfect_power
-- name    : edenic_semiprime_not_perfect_power
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T17:21:07.989458+00:00
-- url     : https://prove2.me/theorems/524dae99-0241-47bf-ae73-0b4fc8b4ea6c
-- title:
--   Edenic semiprimes are not perfect powers
-- statement:
--   No Edenic semiprime is a perfect power: there do not exist $a$ and $k \ge 2$ with $a^k = n$.
--
--   Edenic semiprimes are squarefree (`edenic_semiprime_squarefree`). Suppose $n = a^k$ with $k \ge 2$. The base cannot be $0$ or $1$, since $0^k = 0$ and $1^k = 1$ never equal $n \ge 15$; thus $a \ge 2$ and some prime $q$ divides $a$ (`Nat.exists_prime_and_dvd`). Then $q^k \mid a^k = n$ (by `pow_dvd_pow_of_dvd`) and, since $k \ge 2$, $q^2 \mid q^k$ (by `pow_dvd_pow`), so $q^2 \mid n$. Squarefreeness says any $x$ with $x^2 \mid n$ is a unit — for naturals, $x = 1$ (`Nat.isUnit_iff`) — contradicting $q \neq 1$ for prime $q$.
--
--   **Formalization.** `Nat.isUnit_iff` converts the `IsUnit` produced by squarefreeness into $q = 1$, contradicted by `hq.ne_one`; the small-base case ($a < 2$) is disposed of by `omega`/`nlinarith` against $a^k = n \ge 15$.
--
--   **Reuse.** Reduction to `edenic_semiprime_squarefree` (itself a reduction to `twin_primes_coprime`). Complements `edenic_semiprime_not_square`, which rules out only $k = 2$: here *every* exponent $k \ge 2$ is impossible.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_squarefree

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_squarefree

theorem edenic_semiprime_not_perfect_power (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬∃ a k : ℕ, 2 ≤ k ∧ a ^ k = n := by
  sorry
