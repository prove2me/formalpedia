-- Prove2me | solution 1 for EulerTwoSquares.euler_gcd_pair_factors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:20:16.406106+00:00
-- url     : https://prove2.me/submissions/59ff3fe1-09ce-420d-9b53-5635bcd99496

-- Sol generated from Algebra/EulerTwoSquaresCore.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_eq_of_dvd_prime_mul_prime
import Theorems.Thm_EulerTwoSquares_euler_gcd_proper
import Theorems.Thm_EulerTwoSquares_euler_gcd_proper_add

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




/-- **Euler's method on a semiprime.**  Two essentially distinct representations of `N = p*q`
(`p`, `q` prime) produce, via a single gcd, one of the two prime factors. -/
theorem euler_extraction_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {a b c d : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a ^ 2 + b ^ 2 = (p * q : ℕ)) (h2 : c ^ 2 + d ^ 2 = (p * q : ℕ))
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) = p ∨
      Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) = q := by
  have hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2 := by rw [h1, h2]
  obtain ⟨hlow, hhigh⟩ := euler_gcd_proper ha hb hc hd hN hne1 hne2
  set g : ℕ := Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) with hg
  have hgdvd : (g : ℤ) ∣ (a ^ 2 + b ^ 2) := Int.gcd_dvd_right _ _
  rw [h1] at hgdvd hhigh
  have hgN : g ∣ p * q := by exact_mod_cast hgdvd
  have hlt : g < p * q := by exact_mod_cast hhigh
  exact eq_of_dvd_prime_mul_prime hp hq hgN hlow hlt



/-! ## The degenerate boundary: representations with a zero part

Nothing in Euler's method really needs the parts to be strictly positive.  The only place
positivity was used above is the strict Cauchy–Schwarz step `0 < a*c + b*d`, and that step
survives on the boundary of the cone: if a scalar product degenerates then the two
representations are supported on complementary coordinates, which is exactly what the
essential-distinctness hypotheses forbid.  (Example: `25 = 5² + 0² = 3² + 4²`,
`gcd(5*4 - 0*3, 25) = 5`.) -/







open EulerTwoSquares in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a ^ 2 + b ^ 2 = (p * q : ℕ)) (h2 : c ^ 2 + d ^ 2 = (p * q : ℕ))
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) * Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) = p * q := by
  have hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2 := by rw [h1, h2]
  have hg1 := euler_extraction_semiprime hp hq ha hb hc hd h1 h2 hne1 hne2
  -- the conjugate gcd is also `p` or `q`
  have hg2 : Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) = p ∨
      Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) = q := by
    obtain ⟨hlow, hhigh⟩ := euler_gcd_proper_add ha hb hc hd hN hne1 hne2
    set g₂ : ℕ := Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) with hg₂
    have hgdvd : (g₂ : ℤ) ∣ (a ^ 2 + b ^ 2) := Int.gcd_dvd_right _ _
    rw [h1] at hgdvd hhigh
    exact eq_of_dvd_prime_mul_prime hp hq (by exact_mod_cast hgdvd) hlow (by exact_mod_cast hhigh)
  -- `N` divides the product of the two cross terms, so each prime divides one of the gcds
  have hprod : (a ^ 2 + b ^ 2) ∣ (a * d - b * c) * (a * d + b * c) := dvd_cross_mul_cross hN
  have key : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ (a ^ 2 + b ^ 2) →
      r ∣ Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) ∨
        r ∣ Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) := by
    intro r hr hrN
    have hri : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
    rcases hri.2.2 _ _ (hrN.trans hprod) with h | h
    · left
      exact_mod_cast Int.dvd_gcd h hrN
    · right
      exact_mod_cast Int.dvd_gcd h hrN
  have hpN : (p : ℤ) ∣ (a ^ 2 + b ^ 2) := by rw [h1]; exact_mod_cast Dvd.intro q rfl
  have hqN : (q : ℤ) ∣ (a ^ 2 + b ^ 2) := by rw [h1]; exact_mod_cast Dvd.intro_left p rfl
  have hpdvd := key p hp hpN
  have hqdvd := key q hq hqN
  rcases hg1 with e1 | e1
  · rcases hg2 with e2 | e2
    · exfalso
      rcases hqdvd with hqd | hqd
      · rw [e1] at hqd; exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqd).symm
      · rw [e2] at hqd; exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqd).symm
    · rw [e1, e2]
  · rcases hg2 with e2 | e2
    · rw [e1, e2]; exact Nat.mul_comm q p
    · exfalso
      rcases hpdvd with hpd | hpd
      · rw [e1] at hpd; exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hpd)
      · rw [e2] at hpd; exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hpd)
