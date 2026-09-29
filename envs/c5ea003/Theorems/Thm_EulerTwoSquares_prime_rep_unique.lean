-- Prove2me | Theorems.Thm_EulerTwoSquares_prime_rep_unique
-- name    : EulerTwoSquares.prime_rep_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:46:07.687108+00:00
-- url     : https://prove2.me/theorems/d9f9f721-39b8-49ea-bbec-187a346636a7
-- title:
--   Uniqueness of the two-square representation of a prime.
-- statement:
--   **Uniqueness of the two-square representation of a prime.**  A direct corollary of
--   Euler's extraction theorem: a second essentially distinct representation would produce a
--   proper nontrivial divisor of the prime.
--
--   ```lean
--   theorem EulerTwoSquares.prime_rep_unique{p : ℕ} (hp : p.Prime) {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b)
--       (hc : 0 < c) (hd : 0 < d) (h1 : a ^ 2 + b ^ 2 = (p : ℤ)) (h2 : c ^ 2 + d ^ 2 = (p : ℤ)) :
--       (c = a ∧ d = b) ∨ (d = a ∧ c = b) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresCore.lean#L184

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

theorem EulerTwoSquares.prime_rep_unique{p : ℕ} (hp : p.Prime) {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (h1 : a ^ 2 + b ^ 2 = (p : ℤ)) (h2 : c ^ 2 + d ^ 2 = (p : ℤ)) :
    (c = a ∧ d = b) ∨ (d = a ∧ c = b) := by sorry
