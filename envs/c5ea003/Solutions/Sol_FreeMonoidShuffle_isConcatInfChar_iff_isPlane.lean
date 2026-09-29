-- Prove2me | solution 1 for FreeMonoidShuffle.isConcatInfChar_iff_isPlane
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:11:11.229355+00:00
-- url     : https://prove2.me/submissions/46fdfda3-a632-41fa-b091-d481aabab4ca

-- Thm stub generated from Novelty/FreeMonoidCharacters.lean
import Mathlib
import Definitions.Def_Novelty_FreeMonoidCharacters
import Definitions.Def_Novelty_FreeMonoidUnshuffle
/-
# Characters and infinitesimal characters of the bialgebras on a free monoid

This file formalizes the classification sentence of the paper *Various bialgebras of
representative functions on free monoids*:

> ... the graded noncommutative co-commutative bialgebras of polynomials having,
> for the concatenation, only Kleene stars of the planes as characters, or equivalently,
> only the planes are infinitesimal characters (thanks to a Ree's theorem like).

Concretely, a *character* of the concatenation bialgebra `(K⟨X⟩, conc, Δ_⧢)` is a linear
form `f` on polynomials which is multiplicative for concatenation, i.e. a function
`f : X* → K` with `f(1) = 1` and `f(uv) = f(u) f(v)`; a *plane* is a homogeneous element
of degree one, i.e. a linear form supported on the alphabet; and the *Kleene star* of the
plane `ℓ = Σ_x c_x x` is `ℓ* = Σ_n ℓ^n`, whose coefficient at the word `w = x_1 ⋯ x_n`
is `c_{x_1} ⋯ c_{x_n}`.

Main results:

* `isConcatCharacter_iff_planeStar` : the characters of the concatenation bialgebra are
  exactly the Kleene stars of planes.
* `isConcatInfChar_iff_isPlane` : the infinitesimal characters of the concatenation
  bialgebra are exactly the planes.
* `isShuffleCharacter_expPlane` : dually, the exponential of a plane is a character of
  the shuffle algebra (a group-like series for the unshuffle coproduct).
* `shuffleCharacter_pow_letter` : any shuffle character has divided-power values along a
  single letter, `f(aⁿ) = f(a)ⁿ / n!` — the one-letter case of Ree's theorem.
-/

open FreeMonoidShuffle

variable {X : Type*} {K : Type*}

/-! ## The counit -/




variable [CommRing K]

/-! ## Characters of the concatenation bialgebra -/








/-! ## Infinitesimal characters of the concatenation bialgebra -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FMS

theorem counit_nil {K : Type*} [Zero K] [One K] : counit ([] : List X) = (1 : K) := rfl

theorem counit_cons {K : Type*} [Zero K] [One K] (a : X) (w : List X) :
    counit (a :: w) = (0 : K) := rfl

theorem isConcatInfChar_iff_isPlane {K : Type*} [CommRing K] (g : List X → K) :
    IsConcatInfChar g ↔ IsPlane g := by
  constructor
  · intro h
    have h0 : g ([] : List X) = 0 := by
      have hh := h [] []
      rw [List.append_nil, counit_nil, mul_one, one_mul] at hh
      linear_combination -hh
    intro w hw
    match w with
    | [] => exact h0
    | [a] => exact absurd rfl hw
    | a :: b :: t =>
      have hh := h [a] (b :: t)
      rw [counit_cons, counit_cons, mul_zero, zero_mul, add_zero] at hh
      simpa using hh
  · intro h u v
    have h0 : g ([] : List X) = 0 := h [] (by simp)
    match u, v with
    | [], v =>
      rw [List.nil_append, counit_nil, h0, zero_mul, one_mul, zero_add]
    | a :: u, [] =>
      rw [List.append_nil, counit_nil, counit_cons, h0, mul_one, mul_zero, add_zero]
    | a :: u, b :: v =>
      have h1 : g ((a :: u) ++ (b :: v)) = 0 := by
        refine h _ ?_
        simp only [List.length_append, List.length_cons]
        omega
      rw [h1, counit_cons, counit_cons, mul_zero, zero_mul, add_zero]

/-! ### The deconcatenation coproduct, by counts -/

end FMS

theorem solution (g : List X → K) : IsConcatInfChar g ↔ IsPlane g :=
  FMS.isConcatInfChar_iff_isPlane g
