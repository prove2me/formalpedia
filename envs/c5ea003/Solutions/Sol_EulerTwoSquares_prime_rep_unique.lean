-- Prove2me | solution 1 for EulerTwoSquares.prime_rep_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:43:35.673915+00:00
-- url     : https://prove2.me/submissions/aecd0311-35c4-45a3-b511-1e6b4b819638

-- Sol generated from Algebra/EulerTwoSquaresCore.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_euler_gcd_proper

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
theorem solution{p : ℕ} (hp : p.Prime) {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (h1 : a ^ 2 + b ^ 2 = (p : ℤ)) (h2 : c ^ 2 + d ^ 2 = (p : ℤ)) :
    (c = a ∧ d = b) ∨ (d = a ∧ c = b) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hne1' : ¬(c = a ∧ d = b) := fun h => hne1 h.1 h.2
  have hne2' : ¬(d = a ∧ c = b) := fun h => hne2 h.1 h.2
  have hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2 := by rw [h1, h2]
  obtain ⟨hlow, hhigh⟩ := euler_gcd_proper ha hb hc hd hN hne1' hne2'
  set g : ℕ := Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) with hg
  have hgdvd : (g : ℤ) ∣ (a ^ 2 + b ^ 2) := Int.gcd_dvd_right _ _
  rw [h1] at hgdvd hhigh
  have : g ∣ p := by exact_mod_cast hgdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp g this) with h | h
  · omega
  · rw [h] at hhigh; simp at hhigh
