-- Prove2me | Theorems.Thm_edenic_semiprime_gcd
-- name    : edenic_semiprime_gcd
-- status  : Open
-- author  : @mwm
-- created : 2026-11-25T07:28:33.939593+00:00
-- url     : https://prove2.me/theorems/93d0e903-9525-414f-8688-86dedbd985ef
-- title:
--   Distinct Edenic semiprimes are coprime except for the cluster {15, 35}
-- statement:
--   Two *distinct* Edenic semiprimes are either coprime, or they are exactly the cluster $\{15, 35\}$:
--   $$\gcd(m, n) = 1 \quad\text{or}\quad \{m, n\} = \{15, 35\}.$$
--
--   Write $m = p(p+2)$, $n = q(q+2)$. If the twin pairs $\{p, p+2\}$ and $\{q, q+2\}$ are disjoint, any common prime divisor of $m$ and $n$ would lie in both pairs — impossible — so $m$ and $n$ are coprime. If the pairs share a prime, that prime hinges two twin pairs and hence equals $5$ by `prime_in_two_twin_pairs` (imported); the shared-prime cases give $m = 35, n = 15$ or $m = 15, n = 35$ (the case $p = q$ would make $m = n$, excluded), and $\{15, 35\}$ is the result either way.
--
--   **Formalization.** Case on $p = q \lor p = q+2 \lor p+2 = q$; in the disjoint case, `Nat.coprime_iff_gcd_eq_one` plus `Nat.exists_prime_and_dvd` on a nontrivial gcd produces a shared prime, contradicting disjointness; the hinge cases evaluate to $15$ and $35$ by `decide`.
--
--   **Reuse.** Reduction to `prime_in_two_twin_pairs`. This is the complete classification of common factors of the family: the only obstruction to coprimality is the hinge prime $5$, exactly the shared factor of the cluster.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_prime_in_two_twin_pairs

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_prime_in_two_twin_pairs

theorem edenic_semiprime_gcd (m n : ℕ) (hm : IsEdenicSemiprime m)
    (hn : IsEdenicSemiprime n) (hmn : m ≠ n) :
    m.Coprime n ∨ {m, n} = ({15, 35} : Finset ℕ) := by
  sorry
