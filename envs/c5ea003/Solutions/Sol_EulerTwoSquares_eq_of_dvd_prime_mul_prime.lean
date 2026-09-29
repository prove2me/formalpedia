-- Prove2me | solution 1 for EulerTwoSquares.eq_of_dvd_prime_mul_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:52:14.698184+00:00
-- url     : https://prove2.me/submissions/5102ab3e-600f-4c94-a796-bf65a6427430

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







theorem solution{p q g : ℕ} (hp : p.Prime) (hq : q.Prime) (hg : g ∣ p * q)
    (h1 : 1 < g) (h2 : g < p * q) : g = p ∨ g = q := by
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp (Nat.gcd g p) (Nat.gcd_dvd_right g p)) with hk | hk
  · -- `g` is coprime to `p`, hence divides `q`
    have hcop : Nat.Coprime g p := hk
    have : g ∣ q := (Nat.Coprime.dvd_of_dvd_mul_left hcop hg)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq g this) with h | h
    · omega
    · exact Or.inr h
  · -- `p ∣ g`
    have hpg : p ∣ g := hk ▸ Nat.gcd_dvd_left g p
    obtain ⟨m, hm⟩ := hpg
    have hmq : m ∣ q := by
      have : p * m ∣ p * q := hm ▸ hg
      exact (mul_dvd_mul_iff_left hp.pos.ne').1 this
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq m hmq) with h | h
    · left; rw [hm, h, mul_one]
    · exfalso; rw [h] at hm; omega
