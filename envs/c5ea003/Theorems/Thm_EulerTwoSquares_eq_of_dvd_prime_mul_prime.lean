-- Prove2me | Theorems.Thm_EulerTwoSquares_eq_of_dvd_prime_mul_prime
-- name    : EulerTwoSquares.eq_of_dvd_prime_mul_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:44:05.67927+00:00
-- url     : https://prove2.me/theorems/1ac63943-97f6-4211-ad2d-1ed04fe4cc90
-- title:
--   Divisors of a product of two primes.
-- statement:
--   Divisors of a product of two primes.
--
--   ```lean
--   theorem EulerTwoSquares.eq_of_dvd_prime_mul_prime{p q g : ℕ} (hp : p.Prime) (hq : q.Prime) (hg : g ∣ p * q)
--       (h1 : 1 < g) (h2 : g < p * q) : g = p ∨ g = q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresCore.lean#L205

-- Thm stub generated from Algebra/EulerTwoSquaresCore.lean
import Mathlib

/-!
# Euler's factorization method: the exact algebra of the combination step

Euler's factorisation method takes an integer `N` presented in **two essentially different
ways** as a sum of two squares,

`N = a² + b² = c² + d²`,

and extracts a nontrivial factor of `N` from the *cross term* `a*d - b*c`, namely
`gcd(a*d - b*c, N)`.  Conceptually the cross term is `Im (z₁ * conj z₂)` for the two Gaussian
integers `z₁ = a + b i`, `z₂ = c + d i` of norm `N`.

This file proves the algebraic core of the method, **unconditionally on any primality
assumption**:

* `EulerTwoSquares.rigidity` — the rigidity lemma: `a*d = b*c` together with
  `a*c + b*d = a² + b²` forces `(c,d) = (a,b)`.  This is the equality case of
  Cauchy–Schwarz over `ℤ`, proved by pure linear algebra.
* `EulerTwoSquares.not_dvd_cross` — `N` never divides the cross term unless the two
  representations coincide.
* `EulerTwoSquares.not_isCoprime_cross` — the cross term is never coprime to `N` unless the
  two representations coincide after a swap.
* `EulerTwoSquares.euler_gcd_proper` — **the main theorem**: for positive `a,b,c,d` with
  `a² + b² = c² + d² = N` and the two representations essentially distinct,
  `1 < gcd(a*d - b*c, N) < N`.  So Euler's extraction *always* produces a proper nontrivial
  divisor; no primality, no smoothness, no genericity hypothesis is needed.
* `EulerTwoSquares.euler_extraction_semiprime` — for `N = p*q` a product of two primes the
  extracted divisor is exactly `p` or `q`.
* `EulerTwoSquares.prime_rep_unique` — as an immediate corollary, a prime has an essentially
  unique representation as a sum of two squares.

The proofs use only the two Brahmagupta–Fibonacci identities and integrality; in particular
they do not use unique factorisation in `ℤ[i]`.
-/


/-! ## The two Brahmagupta–Fibonacci identities -/




/-! ## Rigidity: the equality case of Cauchy–Schwarz over `ℤ` -/


/-! ## The two failure modes are impossible -/





/-! ## Euler's extraction theorem -/

theorem EulerTwoSquares.eq_of_dvd_prime_mul_prime{p q g : ℕ} (hp : p.Prime) (hq : q.Prime) (hg : g ∣ p * q)
    (h1 : 1 < g) (h2 : g < p * q) : g = p ∨ g = q := by sorry
