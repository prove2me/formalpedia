-- Prove2me | Theorems.Thm_EulerTwoSquares_rigidity
-- name    : EulerTwoSquares.rigidity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:37:35.363267+00:00
-- url     : https://prove2.me/theorems/cdc6e455-c8b1-4e5e-8c1a-8fbf173957d0
-- title:
--   Rigidity.
-- statement:
--   **Rigidity.**  If the "imaginary part" `a*d - b*c` of `z₁ * conj z₂` vanishes and the
--   "real part" `a*c + b*d` attains the maximal value `a² + b²`, then `z₂ = z₁`.
--   Only `0 < a² + b²` is needed; no relation between the norms is assumed.
--
--   ```lean
--   theorem EulerTwoSquares.rigidity{a b c d : ℤ} (hpos : 0 < a ^ 2 + b ^ 2) (hcross : a * d = b * c)
--       (hdot : a * c + b * d = a ^ 2 + b ^ 2) : c = a ∧ d = b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresCore.lean#L59

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

theorem EulerTwoSquares.rigidity{a b c d : ℤ} (hpos : 0 < a ^ 2 + b ^ 2) (hcross : a * d = b * c)
    (hdot : a * c + b * d = a ^ 2 + b ^ 2) : c = a ∧ d = b := by sorry
