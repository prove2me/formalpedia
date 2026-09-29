-- Prove2me | solution 1 for EulerTwoSquares.prime_not_dvd_cross_both
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:00:47.162214+00:00
-- url     : https://prove2.me/submissions/c9f488d6-e51c-434e-a4ad-37132ee49010

-- Sol generated from Algebra/EulerTwoSquaresCount.lean
import Mathlib

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




theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp4 : p % 4 = 1)
    {e f a b : ℤ} (he : 0 < e) (hf : 0 < f)
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hab : a ^ 2 + b ^ 2 = (p : ℤ) * q) :
    ¬ ((p : ℤ) ∣ (a * f - b * e) ∧ (p : ℤ) ∣ (a * f + b * e)) := by
  rintro ⟨h1, h2⟩
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpe : ¬ ((p : ℤ) ∣ e) := prime_not_dvd_part he hf hef
  have hpf : ¬ ((p : ℤ) ∣ f) := prime_not_dvd_part hf he (by linarith)
  have hp2 : ¬ ((p : ℤ) ∣ 2) := by
    intro hd
    have h' : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hd
    have h'' : p ≤ 2 := by exact_mod_cast h'
    have := hp.two_le
    omega
  have h2af : (p : ℤ) ∣ 2 * (a * f) := by
    have hrw : 2 * (a * f) = (a * f - b * e) + (a * f + b * e) := by ring
    rw [hrw]; exact dvd_add h1 h2
  have h2be : (p : ℤ) ∣ 2 * (b * e) := by
    have hrw : 2 * (b * e) = (a * f + b * e) - (a * f - b * e) := by ring
    rw [hrw]; exact dvd_sub h2 h1
  have ha : (p : ℤ) ∣ a :=
    (hpi.dvd_mul.1 ((hpi.dvd_mul.1 h2af).resolve_left hp2)).resolve_right hpf
  have hb : (p : ℤ) ∣ b :=
    (hpi.dvd_mul.1 ((hpi.dvd_mul.1 h2be).resolve_left hp2)).resolve_right hpe
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hpne : (p : ℤ) ≠ 0 := by
    have := hp.two_le; positivity
  have hcancel : (p : ℤ) * ((p : ℤ) * (a' ^ 2 + b' ^ 2)) = (p : ℤ) * (q : ℤ) := by
    linear_combination hab
  have hq' : (p : ℤ) * (a' ^ 2 + b' ^ 2) = (q : ℤ) := mul_left_cancel₀ hpne hcancel
  have hpdq : (p : ℤ) ∣ (q : ℤ) := ⟨a' ^ 2 + b' ^ 2, hq'.symm⟩
  have : p ∣ q := by exact_mod_cast hpdq
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 this)
