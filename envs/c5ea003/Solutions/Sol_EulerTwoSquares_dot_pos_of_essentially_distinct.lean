-- Prove2me | solution 1 for EulerTwoSquares.dot_pos_of_essentially_distinct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:50:51.488628+00:00
-- url     : https://prove2.me/submissions/cda4cd5b-64a2-43e6-b2c4-2eed98191d77

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







theorem solution{a b c d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hNpos : 0 < a ^ 2 + b ^ 2) (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2)
    (hne2 : ¬(d = a ∧ c = b)) : 0 < a * c + b * d := by
  rcases lt_or_eq_of_le (by positivity : (0 : ℤ) ≤ a * c + b * d) with h | h
  · exact h
  exfalso
  have hac : a * c = 0 := by nlinarith [mul_nonneg ha hc, mul_nonneg hb hd]
  have hbd : b * d = 0 := by nlinarith [mul_nonneg ha hc, mul_nonneg hb hd]
  rcases mul_eq_zero.1 hac with ha0 | hc0
  · rcases mul_eq_zero.1 hbd with hb0 | hd0
    · rw [ha0, hb0] at hNpos; simp at hNpos
    · -- `a = 0`, `d = 0`: then `c² = b²` and the two representations are swaps
      have hcb : c = b := by
        have hfac : (c - b) * (c + b) = 0 := by rw [ha0, hd0] at hN; linarith
        rcases mul_eq_zero.1 hfac with h1 | h1
        · linarith
        · have : c = 0 := by linarith
          have : b = 0 := by linarith
          omega
      exact hne2 ⟨by rw [hd0, ha0], hcb⟩
  · rcases mul_eq_zero.1 hbd with hb0 | hd0
    · -- `c = 0`, `b = 0`: then `d² = a²`
      have hda : d = a := by
        have hfac : (d - a) * (d + a) = 0 := by rw [hc0, hb0] at hN; linarith
        rcases mul_eq_zero.1 hfac with h1 | h1
        · linarith
        · have : d = 0 := by linarith
          have : a = 0 := by linarith
          omega
      exact hne2 ⟨hda, by rw [hc0, hb0]⟩
    · rw [hc0, hd0] at hN; simp at hN; omega
