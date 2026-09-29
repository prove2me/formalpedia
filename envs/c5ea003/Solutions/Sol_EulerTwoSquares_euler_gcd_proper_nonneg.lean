-- Prove2me | solution 1 for EulerTwoSquares.euler_gcd_proper_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:26:03.516904+00:00
-- url     : https://prove2.me/submissions/9265776c-062a-41e0-ba5d-ae6e65589982

-- Sol generated from Algebra/EulerTwoSquaresCore.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_not_dvd_cross_add_nonneg
import Theorems.Thm_EulerTwoSquares_not_dvd_cross_nonneg

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



/-- The product of the two cross terms is a multiple of `a² + b²` whenever the two
representations have the same value: this is the divisibility that drives Euler's method. -/
theorem dvd_cross_mul_cross {a b c d : ℤ} (h : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2) :
    (a ^ 2 + b ^ 2) ∣ (a * d - b * c) * (a * d + b * c) :=
  ⟨a ^ 2 - c ^ 2, by linear_combination a ^ 2 * h⟩

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
theorem solution{a b c d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hNpos : 0 < a ^ 2 + b ^ 2) (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2)
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    1 < Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) ∧
      ((Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) : ℤ) < a ^ 2 + b ^ 2) := by
  set N : ℤ := a ^ 2 + b ^ 2 with hNdef
  set g : ℕ := Int.gcd (a * d - b * c) N with hg
  have hgdvdN : (g : ℤ) ∣ N := Int.gcd_dvd_right _ _
  have hgdvdc : (g : ℤ) ∣ (a * d - b * c) := Int.gcd_dvd_left _ _
  have hg1 : 1 < g := by
    rcases Nat.lt_or_ge 1 g with h | h
    · exact h
    · interval_cases g
      · exfalso
        have hz : N = 0 := (Int.gcd_eq_zero_iff.1 hg.symm).2
        omega
      · exfalso
        have hcop : IsCoprime (a * d - b * c) N := Int.isCoprime_iff_gcd_eq_one.2 hg.symm
        exact not_dvd_cross_add_nonneg ha hb hc hd hNpos hN hne1 hne2
          ((hcop.symm).dvd_of_dvd_mul_left (dvd_cross_mul_cross hN))
  refine ⟨hg1, ?_⟩
  rcases lt_or_eq_of_le (Int.le_of_dvd hNpos hgdvdN) with h | h
  · exact h
  · exfalso
    have hdvdN : N ∣ (a * d - b * c) := by rw [← h]; exact hgdvdc
    exact not_dvd_cross_nonneg ha hb hc hd hNpos hN hne1 hne2 hdvdN
