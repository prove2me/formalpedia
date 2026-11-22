-- Prove2me | Theorems.Thm_Erdos390_dvd_of_bounded_prime_factors
-- name    : Erdos390.dvd_of_bounded_prime_factors
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-06T05:23:59.292092+00:00
-- url     : https://prove2.me/theorems/c2a7dbd6-502c-4110-b2d2-cf78cf24c79f
-- title:
--   Divisibility from prime valuation bounds on bounded prime support
-- statement:
--   **Divisibility from Prime Valuation Bounds on Bounded Prime Support**
--
--   Let $D, P, B \in \mathbb{N}$ with $D > 0$ and $P > 0$. Suppose that every prime factor of $D$ is bounded by $B$:
--   $$\forall \ell \in \mathbb{P},\quad \ell \mid D \implies \ell \le B.$$
--   Suppose furthermore that for all primes $\ell \le B$, the $\ell$-adic valuation of $D$ is bounded by that of $P$:
--   $$\forall \ell \in \mathbb{P},\quad \ell \le B \implies v_\ell(D) \le v_\ell(P).$$
--   Then $D$ divides $P$:
--   $$D \mid P.$$
--
--   This establishes the fundamental arithmetic bridge (Shouqiao Wang's `CentralAnchorTailDivisibility.lean`) showing that finite support prime valuation bounds imply literal natural-number divisibility.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdős Problem 390, Section 10, CentralAnchorTailDivisibility.lean (GitHub 61325b1)

import Mathlib

namespace Erdos390

theorem dvd_of_bounded_prime_factors
    {D P B : ℕ} (hD : D ≠ 0) (hP : P ≠ 0)
    (hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ D → ℓ ≤ B)
    (hval : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ B → D.factorization ℓ ≤ P.factorization ℓ) :
    D ∣ P := by sorry

end Erdos390
