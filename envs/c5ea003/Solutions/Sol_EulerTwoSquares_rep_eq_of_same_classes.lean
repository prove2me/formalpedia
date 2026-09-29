-- Prove2me | solution 1 for EulerTwoSquares.rep_eq_of_same_classes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:37:14.044046+00:00
-- url     : https://prove2.me/submissions/a902e418-61f5-47bb-93d6-b55053e7215c

-- Sol generated from Algebra/EulerTwoSquaresCount.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_cross_dvd_of_same_class
import Theorems.Thm_EulerTwoSquares_not_dvd_cross

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





/-! ## The class bits attached to a representation -/

variable {p q : ℕ}





/-! ## The Brahmagupta construction: four ordered representations -/



/-! ## Exactly two representations -/


/-! ## The empty cells: a prime `3 mod 4` to an odd power -/




open EulerTwoSquares in
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e f g h a₁ b₁ a₂ b₂ : ℤ} (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hh : 0 < h)
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hgh : g ^ 2 + h ^ 2 = (q : ℤ))
    (ha₁ : 0 < a₁) (hb₁ : 0 < b₁) (ha₂ : 0 < a₂) (hb₂ : 0 < b₂)
    (hr1 : a₁ ^ 2 + b₁ ^ 2 = (p : ℤ) * q) (hr2 : a₂ ^ 2 + b₂ ^ 2 = (p : ℤ) * q)
    (hsp : ((p : ℤ) ∣ (a₁ * f - b₁ * e)) ↔ ((p : ℤ) ∣ (a₂ * f - b₂ * e)))
    (hsq : ((q : ℤ) ∣ (a₁ * h - b₁ * g)) ↔ ((q : ℤ) ∣ (a₂ * h - b₂ * g))) :
    a₂ = a₁ ∧ b₂ = b₁ := by
  have hdp : (p : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) :=
    cross_dvd_of_same_class (q := q) hp he hf hef hr1 hr2 hsp
  have hr1' : a₁ ^ 2 + b₁ ^ 2 = (q : ℤ) * p := by rw [hr1]; ring
  have hr2' : a₂ ^ 2 + b₂ ^ 2 = (q : ℤ) * p := by rw [hr2]; ring
  have hdq : (q : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) :=
    cross_dvd_of_same_class (q := p) hq hg hh hgh hr1' hr2' hsq
  have hcop : IsCoprime ((p : ℤ)) ((q : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using (Nat.coprime_primes hp hq).2 hpq
  have hdvd : ((p : ℤ) * q) ∣ (a₁ * b₂ - a₂ * b₁) := hcop.mul_dvd hdp hdq
  by_contra hcon
  have hN : a₂ ^ 2 + b₂ ^ 2 = a₁ ^ 2 + b₁ ^ 2 := by rw [hr1, hr2]
  refine not_dvd_cross ha₁ hb₁ ha₂ hb₂ hN hcon ?_
  rw [hr1]
  have hrw : a₁ * b₂ - b₁ * a₂ = a₁ * b₂ - a₂ * b₁ := by ring
  rw [hrw]
  exact hdvd
