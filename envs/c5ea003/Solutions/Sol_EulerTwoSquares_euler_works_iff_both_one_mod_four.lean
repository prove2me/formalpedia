-- Prove2me | solution 1 for EulerTwoSquares.euler_works_iff_both_one_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:40:45.864179+00:00
-- url     : https://prove2.me/submissions/c90cbded-a886-4ac0-ae04-3dac51ba6592

-- Sol generated from Algebra/EulerTwoSquaresCount.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_exactly_two_reps
import Theorems.Thm_EulerTwoSquares_no_rep_of_three_mod_four

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
theorem solution(hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    (∃ a b c d : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a ^ 2 + b ^ 2 = (p : ℤ) * q ∧
        c ^ 2 + d ^ 2 = (p : ℤ) * q ∧ ¬(c = a ∧ d = b) ∧ ¬(d = a ∧ c = b)) ↔
      (p % 4 = 1 ∧ q % 4 = 1) := by
  have hpodd : p % 4 = 1 ∨ p % 4 = 3 := by
    have : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    omega
  have hqodd : q % 4 = 1 ∨ q % 4 = 3 := by
    have : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · exact absurd h hq2
      · exact h
    omega
  constructor
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, hab, hcd, hne1, hne2⟩
    have hcast : a ^ 2 + b ^ 2 = ((p * q : ℕ) : ℤ) := by push_cast; exact hab
    constructor
    · rcases hpodd with h | h
      · exact h
      · exfalso
        refine no_rep_of_three_mod_four hp h (Dvd.intro q rfl) ?_ a b hcast
        intro hdvd
        have : p ∣ q := by
          have h2 : p * p ∣ p * q := by
            rcases hdvd with ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
          exact (mul_dvd_mul_iff_left hp.pos.ne').1 h2
        exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 this)
    · rcases hqodd with h | h
      · exact h
      · exfalso
        refine no_rep_of_three_mod_four hq h (Dvd.intro_left p rfl) ?_ a b hcast
        intro hdvd
        have : q ∣ p := by
          have h2 : q * q ∣ q * p := by
            rcases hdvd with ⟨k, hk⟩; exact ⟨k, by rw [mul_comm q p, hk]; ring⟩
          exact (mul_dvd_mul_iff_left hq.pos.ne').1 h2
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 this).symm
  · rintro ⟨hp4, hq4⟩
    obtain ⟨A, B, C, D, hA, hB, hC, hD, hAB, hCD, h1, h2, -⟩ :=
      exactly_two_reps hp hq hp4 hq4 hpq
    exact ⟨A, B, C, D, hA, hB, hC, hD, hAB, hCD, h1, h2⟩
