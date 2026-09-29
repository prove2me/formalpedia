-- Prove2me | solution 1 for EulerTwoSquares.rigidity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:37:45.238319+00:00
-- url     : https://prove2.me/submissions/26dcb758-68ee-49e9-a9d0-cf975ea6d062

-- Sol generated from Algebra/EulerTwoSquaresCore.lean
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







/-! ## The degenerate boundary: representations with a zero part

Nothing in Euler's method really needs the parts to be strictly positive.  The only place
positivity was used above is the strict Cauchy–Schwarz step `0 < a*c + b*d`, and that step
survives on the boundary of the cone: if a scalar product degenerates then the two
representations are supported on complementary coordinates, which is exactly what the
essential-distinctness hypotheses forbid.  (Example: `25 = 5² + 0² = 3² + 4²`,
`gcd(5*4 - 0*3, 25) = 5`.) -/







theorem solution{a b c d : ℤ} (hpos : 0 < a ^ 2 + b ^ 2) (hcross : a * d = b * c)
    (hdot : a * c + b * d = a ^ 2 + b ^ 2) : c = a ∧ d = b := by
  have hne : (a ^ 2 + b ^ 2) ≠ 0 := ne_of_gt hpos
  have hc : (a ^ 2 + b ^ 2) * c = (a ^ 2 + b ^ 2) * a := by
    linear_combination a * hdot - b * hcross
  have hca : c = a := mul_left_cancel₀ hne hc
  refine ⟨hca, ?_⟩
  rcases eq_or_ne b 0 with hb | hb
  · have ha : a ≠ 0 := by
      intro h; rw [h, hb] at hpos; simp at hpos
    have hd0 : a * d = 0 := by rw [hcross, hb]; ring
    have hdz := (mul_eq_zero.1 hd0).resolve_left ha
    rw [hdz, hb]
  · have hbd : b * d = b * b := by rw [hca] at hdot; linear_combination hdot
    exact mul_left_cancel₀ hb hbd
