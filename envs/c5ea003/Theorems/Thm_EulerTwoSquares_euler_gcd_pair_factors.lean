-- Prove2me | Theorems.Thm_EulerTwoSquares_euler_gcd_pair_factors
-- name    : EulerTwoSquares.euler_gcd_pair_factors
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:44:29.79186+00:00
-- url     : https://prove2.me/theorems/d19e63dd-7cd2-49ca-9057-e97c4cdf3d72
-- title:
--   The two gcds recover the whole factorisation.
-- statement:
--   **The two gcds recover the whole factorisation.**  For `N = p*q` a product of two distinct
--   primes, the two cross terms of a pair of essentially distinct representations produce the two
--   prime factors: `gcd(a*d - b*c, N) * gcd(a*d + b*c, N) = p*q`.
--
--   ```lean
--   theorem EulerTwoSquares.euler_gcd_pair_factors{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
--       {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
--       (h1 : a ^ 2 + b ^ 2 = (p * q : ℕ)) (h2 : c ^ 2 + d ^ 2 = (p * q : ℕ))
--       (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
--       Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) * Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) = p * q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresCore.lean#L269

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

theorem EulerTwoSquares.euler_gcd_pair_factors{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a ^ 2 + b ^ 2 = (p * q : ℕ)) (h2 : c ^ 2 + d ^ 2 = (p * q : ℕ))
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) * Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) = p * q := by sorry
