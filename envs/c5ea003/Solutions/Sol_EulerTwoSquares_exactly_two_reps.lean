-- Prove2me | solution 1 for EulerTwoSquares.exactly_two_reps
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:38:59.824824+00:00
-- url     : https://prove2.me/submissions/90cca539-f59d-4558-9ed2-a06d5234c289

-- Sol generated from Algebra/EulerTwoSquaresCount.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_exists_four_reps
import Theorems.Thm_EulerTwoSquares_rep_eq_of_same_classes

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

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Five pairwise distinct elements of `Bool × Bool` cannot exist. -/
theorem pigeonhole_four_classes :
    ∀ v₁ v₂ v₃ v₄ v₅ : Bool × Bool, v₁ ≠ v₂ → v₁ ≠ v₃ → v₁ ≠ v₄ → v₁ ≠ v₅ → v₂ ≠ v₃ →
      v₂ ≠ v₄ → v₂ ≠ v₅ → v₃ ≠ v₄ → v₃ ≠ v₅ → v₄ ≠ v₅ → False := by decide

/-! ## Elementary facts about representations of a prime -/





/-! ## The class bits attached to a representation -/

variable {p q : ℕ}





/-! ## The Brahmagupta construction: four ordered representations -/



/-! ## Exactly two representations -/


/-! ## The empty cells: a prime `3 mod 4` to an odd power -/




open EulerTwoSquares in
theorem solution(hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
    (hpq : p ≠ q) :
    ∃ A B C D : ℤ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧
      A ^ 2 + B ^ 2 = (p : ℤ) * q ∧ C ^ 2 + D ^ 2 = (p : ℤ) * q ∧
      ¬(C = A ∧ D = B) ∧ ¬(D = A ∧ C = B) ∧
      ∀ a b : ℤ, 0 < a → 0 < b → a ^ 2 + b ^ 2 = (p : ℤ) * q →
        (a = A ∧ b = B) ∨ (a = B ∧ b = A) ∨ (a = C ∧ b = D) ∨ (a = D ∧ b = C) := by
  obtain ⟨e, f, g, h, A, B, C, D, ⟨he, hf, hg, hh, hef, hgh⟩, ⟨hA, hB, hC, hD⟩, ⟨hAB, hCD⟩,
    hAneB, hAneC, hAneD, hBneC, hBneD, hCneD⟩ := exists_four_reps hp hq hp4 hq4 hpq
  have hBA : B ^ 2 + A ^ 2 = (p : ℤ) * q := by linarith
  have hDC : D ^ 2 + C ^ 2 = (p : ℤ) * q := by linarith
  refine ⟨A, B, C, D, hA, hB, hC, hD, hAB, hCD, fun hx => hAneC hx.1.symm,
    fun hx => hAneD hx.1.symm, ?_⟩
  intro a b ha hb hab
  by_contra hcon
  have key : ∀ x₁ y₁ x₂ y₂ : ℤ, 0 < x₁ → 0 < y₁ → 0 < x₂ → 0 < y₂ →
      x₁ ^ 2 + y₁ ^ 2 = (p : ℤ) * q → x₂ ^ 2 + y₂ ^ 2 = (p : ℤ) * q → ¬(x₂ = x₁ ∧ y₂ = y₁) →
      ((decide ((p : ℤ) ∣ (x₁ * f - y₁ * e)), decide ((q : ℤ) ∣ (x₁ * h - y₁ * g))) :
          Bool × Bool) ≠
        (decide ((p : ℤ) ∣ (x₂ * f - y₂ * e)), decide ((q : ℤ) ∣ (x₂ * h - y₂ * g))) := by
    intro x₁ y₁ x₂ y₂ h1 h2 h3 h4 hr1 hr2 hne hEq
    exact hne (rep_eq_of_same_classes hp hq hpq he hf hg hh hef hgh h1 h2 h3 h4 hr1 hr2
      (decide_eq_decide.1 (congrArg Prod.fst hEq)) (decide_eq_decide.1 (congrArg Prod.snd hEq)))
  exact pigeonhole_four_classes _ _ _ _ _
    (key a b A B ha hb hA hB hab hAB (fun hx => hcon (Or.inl ⟨hx.1.symm, hx.2.symm⟩)))
    (key a b B A ha hb hB hA hab hBA (fun hx => hcon (Or.inr (Or.inl ⟨hx.1.symm, hx.2.symm⟩))))
    (key a b C D ha hb hC hD hab hCD
      (fun hx => hcon (Or.inr (Or.inr (Or.inl ⟨hx.1.symm, hx.2.symm⟩)))))
    (key a b D C ha hb hD hC hab hDC
      (fun hx => hcon (Or.inr (Or.inr (Or.inr ⟨hx.1.symm, hx.2.symm⟩)))))
    (key A B B A hA hB hB hA hAB hBA (fun hx => hAneB hx.1.symm))
    (key A B C D hA hB hC hD hAB hCD (fun hx => hAneC hx.1.symm))
    (key A B D C hA hB hD hC hAB hDC (fun hx => hAneD hx.1.symm))
    (key B A C D hB hA hC hD hBA hCD (fun hx => hBneC hx.1.symm))
    (key B A D C hB hA hD hC hBA hDC (fun hx => hBneD hx.1.symm))
    (key C D D C hC hD hD hC hCD hDC (fun hx => hCneD hx.1.symm))
