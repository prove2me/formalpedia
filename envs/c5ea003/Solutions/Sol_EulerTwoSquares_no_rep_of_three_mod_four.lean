-- Prove2me | solution 1 for EulerTwoSquares.no_rep_of_three_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:56:06.649908+00:00
-- url     : https://prove2.me/submissions/4f7994ef-e5f6-4537-8bc3-02ad58b7322e

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





/-! ## The class bits attached to a representation -/

variable {p q : ℕ}





/-! ## The Brahmagupta construction: four ordered representations -/



/-! ## Exactly two representations -/


/-! ## The empty cells: a prime `3 mod 4` to an odd power -/




theorem solution{r n : ℕ} (hr : r.Prime) (hr4 : r % 4 = 3) (hdvd : r ∣ n)
    (hsq : ¬ (r ^ 2 ∣ n)) (a b : ℤ) : a ^ 2 + b ^ 2 ≠ (n : ℤ) := by
  intro hab
  haveI := Fact.mk hr
  have hrn : (r : ℤ) ∣ (a ^ 2 + b ^ 2) := by
    rw [hab]; exact_mod_cast Int.natCast_dvd_natCast.2 hdvd
  have h0 : ((a : ZMod r)) ^ 2 + ((b : ZMod r)) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + b ^ 2) r).2 hrn
    push_cast at this
    exact this
  have ha0 : ((a : ZMod r)) = 0 := by
    by_contra hne
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq (y := (b : ZMod r)) hne
      (by linear_combination h0) hr4
  have hb0 : ((b : ZMod r)) = 0 := by
    by_contra hne
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := (a : ZMod r)) hne
      (by linear_combination h0) hr4
  have hra : (r : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a r).1 ha0
  have hrb : (r : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b r).1 hb0
  obtain ⟨a', rfl⟩ := hra
  obtain ⟨b', rfl⟩ := hrb
  have : ((r : ℤ)) ^ 2 ∣ (n : ℤ) := ⟨a' ^ 2 + b' ^ 2, by linear_combination -hab⟩
  exact hsq (by exact_mod_cast this)
