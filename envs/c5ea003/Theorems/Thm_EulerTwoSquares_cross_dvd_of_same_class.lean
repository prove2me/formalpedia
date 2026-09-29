-- Prove2me | Theorems.Thm_EulerTwoSquares_cross_dvd_of_same_class
-- name    : EulerTwoSquares.cross_dvd_of_same_class
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:43:40.76448+00:00
-- url     : https://prove2.me/theorems/32380a70-1b39-4752-b5c3-6d9b5f4332fc
-- title:
--   Two representations of `p*q` with the same `p`-bit satisfy `p ∣ a₁b₂ - a₂b₁`.
-- statement:
--   Two representations of `p*q` with the same `p`-bit satisfy `p ∣ a₁b₂ - a₂b₁`.
--
--   ```lean
--   theorem EulerTwoSquares.cross_dvd_of_same_class(hp : p.Prime) {e f a₁ b₁ a₂ b₂ : ℤ} (he : 0 < e) (hf : 0 < f)
--       (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hr1 : a₁ ^ 2 + b₁ ^ 2 = (p : ℤ) * q)
--       (hr2 : a₂ ^ 2 + b₂ ^ 2 = (p : ℤ) * q)
--       (hsame : ((p : ℤ) ∣ (a₁ * f - b₁ * e)) ↔ ((p : ℤ) ∣ (a₂ * f - b₂ * e))) :
--       (p : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresCount.lean#L133

-- Thm stub generated from Algebra/EulerTwoSquaresCount.lean
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

theorem EulerTwoSquares.cross_dvd_of_same_class(hp : p.Prime) {e f a₁ b₁ a₂ b₂ : ℤ} (he : 0 < e) (hf : 0 < f)
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hr1 : a₁ ^ 2 + b₁ ^ 2 = (p : ℤ) * q)
    (hr2 : a₂ ^ 2 + b₂ ^ 2 = (p : ℤ) * q)
    (hsame : ((p : ℤ) ∣ (a₁ * f - b₁ * e)) ↔ ((p : ℤ) ∣ (a₂ * f - b₂ * e))) :
    (p : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) := by sorry
