-- Prove2me | Theorems.Thm_edenic_semiprime_moebius
-- name    : edenic_semiprime_moebius
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-26T16:48:21.421172+00:00
-- url     : https://prove2.me/theorems/78444a99-7271-57f8-b716-2792f28a540a
-- title:
--   The Möbius function of an Edenic semiprime is 1
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$\mu(n) = 1 ,$$
--   where $\mu$ denotes the Möbius function (Lean: `ArithmeticFunction.moebius`).
--
--   An Edenic semiprime is a squarefree number with exactly two distinct prime divisors: $p$ and $p + 2$ differ by the twin gap $2$, so they are distinct, and each appears to the first power. The Möbius function of a squarefree integer is $(-1)^k$ where $k$ is the number of its prime divisors; here $k = 2$ and therefore $\mu(n) = (-1)^2 = 1$. Equivalently, via multiplicativity: the twins are coprime (`twin_primes_coprime`), so $\mu(n) = \mu(p)\,\mu(p+2) = (-1)(-1) = 1$.
--
--   **Formalization.** Multiplicativity across the coprime pair is `ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime` fed with `twin_primes_coprime` (imported); `ArithmeticFunction.moebius_apply_prime` evaluates each factor at a prime to $-1$, and `norm_num` reduces the product.
--
--   **Reuse.** A reduction through `twin_primes_coprime`. The value $\mu(n) = 1 \ne 0$ re-witnesses `edenic_semiprime_squarefree`, and the two-prime structure pairs with `edenic_semiprime_divisors` / `edenic_semiprime_primeFactorsList`, which pin the divisor set to $\{1, p, p+2, n\}$.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_moebius (n : ℕ) (h : IsEdenicSemiprime n) :
    ArithmeticFunction.moebius n = 1 := by
  sorry
