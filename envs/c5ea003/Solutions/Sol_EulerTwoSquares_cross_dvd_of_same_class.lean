-- Prove2me | solution 1 for EulerTwoSquares.cross_dvd_of_same_class
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:11:25.255636+00:00
-- url     : https://prove2.me/submissions/72924284-838b-4ed6-a361-1848bfe88299

-- Sol generated from Algebra/EulerTwoSquaresCount.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_prime_dvd_cross_or

/-!
# The eligibility class of Euler's method: exactly two representations, or none

Euler's factorisation method needs **two essentially distinct** representations of `N` as a
sum of two squares.  For `N = p*q` a product of two distinct odd primes this file settles
exactly when such a pair exists, and how many representations there are:

* `EulerTwoSquares.exactly_two_reps` — if `p ≠ q` are primes with `p ≡ q ≡ 1 [MOD 4]`, then
  `p*q` has **exactly two** essentially distinct representations as a sum of two positive
  squares: there are explicit `A,B,C,D` such that the ordered positive representations are
  precisely `(A,B), (B,A), (C,D), (D,C)`.
* `EulerTwoSquares.no_rep_of_three_mod_four` — if some prime `r ≡ 3 [MOD 4]` divides `n`
  exactly once, then `n` has **no** representation at all.  This kills the classes
  `(1,3), (3,1), (3,3)` and `(2,3)` of the semiprime table.
* `EulerTwoSquares.euler_works_iff_both_one_mod_four` — the resulting dichotomy for
  `N = p*q` with `p ≠ q` odd primes: two essentially distinct representations exist iff both
  primes are `1 mod 4`.

The "at most two" half is proved by a *class argument* powered by the extraction theorem of
`EulerTwoSquaresCore`: fixing representations `p = e²+f²` and `q = g²+h²`, every
representation `(a,b)` of `p*q` gets a pair of bits

`(⟦p ∣ a f - b e⟧, ⟦q ∣ a h - b g⟧) ∈ Bool × Bool`,

two representations with the same bits have `N ∣ a₁b₂ - a₂b₁`, and then
`EulerTwoSquares.not_dvd_cross` forces them to be equal.  Since `Bool × Bool` has four
elements there are at most four ordered representations, i.e. at most two up to order — and
the Brahmagupta construction produces four.  So the count is exact.
-/

open EulerTwoSquares


/-! ## Elementary facts about representations of a prime -/




/-- A prime does not divide either part of one of its two-square representations. -/
theorem prime_not_dvd_part {p : ℕ} {e f : ℤ} (he : 0 < e) (hf : 0 < f)
    (h : e ^ 2 + f ^ 2 = (p : ℤ)) : ¬ ((p : ℤ) ∣ e) := by
  intro hdvd
  have hlt : e < (p : ℤ) := by nlinarith
  have := Int.le_of_dvd he hdvd
  omega

/-! ## The class bits attached to a representation -/

variable {p q : ℕ}





/-! ## The Brahmagupta construction: four ordered representations -/



/-! ## Exactly two representations -/


/-! ## The empty cells: a prime `3 mod 4` to an odd power -/




open EulerTwoSquares in
theorem solution(hp : p.Prime) {e f a₁ b₁ a₂ b₂ : ℤ} (he : 0 < e) (hf : 0 < f)
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hr1 : a₁ ^ 2 + b₁ ^ 2 = (p : ℤ) * q)
    (hr2 : a₂ ^ 2 + b₂ ^ 2 = (p : ℤ) * q)
    (hsame : ((p : ℤ) ∣ (a₁ * f - b₁ * e)) ↔ ((p : ℤ) ∣ (a₂ * f - b₂ * e))) :
    (p : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpf : ¬ ((p : ℤ) ∣ f) := prime_not_dvd_part hf he (by linarith)
  have key : (p : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) * f := by
    by_cases h1 : (p : ℤ) ∣ (a₁ * f - b₁ * e)
    · have h2 := hsame.1 h1
      have hrw : (a₁ * b₂ - a₂ * b₁) * f = b₂ * (a₁ * f - b₁ * e) - b₁ * (a₂ * f - b₂ * e) := by
        ring
      rw [hrw]; exact dvd_sub (h1.mul_left b₂) (h2.mul_left b₁)
    · have h2 : ¬ ((p : ℤ) ∣ (a₂ * f - b₂ * e)) := fun hh => h1 (hsame.2 hh)
      have h1' := (prime_dvd_cross_or (q := q) hp hef hr1).resolve_left h1
      have h2' := (prime_dvd_cross_or (q := q) hp hef hr2).resolve_left h2
      have hrw : (a₁ * b₂ - a₂ * b₁) * f = b₂ * (a₁ * f + b₁ * e) - b₁ * (a₂ * f + b₂ * e) := by
        ring
      rw [hrw]; exact dvd_sub (h1'.mul_left b₂) (h2'.mul_left b₁)
  exact (hpi.dvd_mul.1 key).resolve_right hpf
