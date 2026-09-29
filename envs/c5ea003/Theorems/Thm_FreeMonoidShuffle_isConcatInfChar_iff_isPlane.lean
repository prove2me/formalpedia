-- Prove2me | Theorems.Thm_FreeMonoidShuffle_isConcatInfChar_iff_isPlane
-- name    : FreeMonoidShuffle.isConcatInfChar_iff_isPlane
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:50:16.424033+00:00
-- url     : https://prove2.me/theorems/05593dc8-1fef-4a39-924d-3a471e3093a6
-- title:
--   **The infinitesimal characters of the concatenation bialgebra are exactly the
-- statement:
--   **The infinitesimal characters of the concatenation bialgebra are exactly the
--   planes.**
--
--   ```lean
--   theorem FreeMonoidShuffle.isConcatInfChar_iff_isPlane(g : List X → K) : IsConcatInfChar g ↔ IsPlane g := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FreeMonoidCharacters.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FreeMonoidCharacters.lean#L101

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

theorem FreeMonoidShuffle.isConcatInfChar_iff_isPlane(g : List X → K) : IsConcatInfChar g ↔ IsPlane g := by sorry
