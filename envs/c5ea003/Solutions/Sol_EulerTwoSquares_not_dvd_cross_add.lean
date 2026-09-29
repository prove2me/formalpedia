-- Prove2me | solution 1 for EulerTwoSquares.not_dvd_cross_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:15:32.777907+00:00
-- url     : https://prove2.me/submissions/0851917e-9791-44e5-9312-fc50a310cffa

-- Sol generated from Algebra/EulerTwoSquaresCore.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_rigidity

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

open EulerTwoSquares

/-! ## The two Brahmagupta–Fibonacci identities -/


/-- Brahmagupta–Fibonacci, "plus" branch. -/
theorem brahmagupta_add (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring


/-! ## Rigidity: the equality case of Cauchy–Schwarz over `ℤ` -/


/-! ## The two failure modes are impossible -/





/-! ## Euler's extraction theorem -/







/-! ## The degenerate boundary: representations with a zero part

Nothing in Euler's method really needs the parts to be strictly positive.  The only place
positivity was used above is the strict Cauchy–Schwarz step `0 < a*c + b*d`, and that step
survives on the boundary of the cone: if a scalar product degenerates then the two
representations are supported on complementary coordinates, which is exactly what the
essential-distinctness hypotheses forbid.  (Example: `25 = 5² + 0² = 3² + 4²`,
`gcd(5*4 - 0*3, 25) = 5`.) -/







open EulerTwoSquares in
theorem solution{a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2) (hne : ¬(d = a ∧ c = b)) :
    ¬ (a ^ 2 + b ^ 2) ∣ (a * d + b * c) := by
  intro hdvd
  set N : ℤ := a ^ 2 + b ^ 2 with hNdef
  have hNpos : 0 < N := by positivity
  have key : (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = N ^ 2 := by
    have := brahmagupta_add a b c d
    rw [hN] at this
    linarith [this]
  have hpos : 0 < a * d + b * c := by positivity
  have hle : N ≤ a * d + b * c := Int.le_of_dvd hpos hdvd
  have hge : a * d + b * c ≤ N := by nlinarith [sq_nonneg (a * c - b * d)]
  have heq : a * d + b * c = N := le_antisymm hge hle
  have hz : a * c - b * d = 0 := by
    have hsq : (a * c - b * d) ^ 2 = 0 := by rw [heq] at key; linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
  exact hne (rigidity hNpos (by linarith) heq)
