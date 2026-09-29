-- Prove2me | Definitions.Def_Novelty_FreeMonoidCharacters
-- name    : Novelty_FreeMonoidCharacters
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:26:54.481821+00:00
-- url     : https://prove2.me/theorems/7dd27f05-f72c-40c4-99fc-cff193e04d42
-- title:
--   Aether Catalog definitions — Novelty_FreeMonoidCharacters
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FreeMonoidCharacters`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FreeMonoidCharacters.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_FreeMonoidShuffle
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

namespace FreeMonoidShuffle

variable {X : Type*} {K : Type*}

/-! ## The counit -/

/-- The counit `ε` of both bialgebras: `ε(w) = 1` if `w` is the empty word, `0` otherwise. -/
def counit [Zero K] [One K] : List X → K
  | [] => 1
  | _ :: _ => 0



section CommRing
variable [CommRing K]

/-! ## Characters of the concatenation bialgebra -/

/-- A character of the concatenation bialgebra: a multiplicative, unital linear form. -/
def IsConcatCharacter (f : List X → K) : Prop :=
  f [] = 1 ∧ ∀ u v : List X, f (u ++ v) = f u * f v

/-- The Kleene star `ℓ*` of the plane `ℓ = Σ_x c_x x`, read off as a function on words:
its coefficient at `w = x_1 ⋯ x_n` is `c_{x_1} ⋯ c_{x_n}`. -/
def planeStar (c : X → K) : List X → K := fun w => (w.map c).prod






/-! ## Infinitesimal characters of the concatenation bialgebra -/

/-- An infinitesimal character of the concatenation bialgebra: a linear form which is a
derivation from the concatenation product to the counit, i.e. `g(uv) = g(u)ε(v) + ε(u)g(v)`. -/
def IsConcatInfChar (g : List X → K) : Prop :=
  ∀ u v : List X, g (u ++ v) = g u * counit v + counit u * g v

/-- A *plane*: a linear form supported by the alphabet, i.e. a homogeneous element of
degree one of the graded dual. -/
def IsPlane (g : List X → K) : Prop := ∀ w : List X, w.length ≠ 1 → g w = 0


end CommRing

/-! ## Characters of the shuffle algebra -/

section Shuffle
variable [CommRing K]

/-- A character of the shuffle algebra, equivalently (by shuffle/unshuffle duality) a
group-like series for the unshuffle coproduct. -/
def IsShuffleCharacter (f : List X → K) : Prop :=
  f [] = 1 ∧ ∀ u v : List X, f u * f v = ((shuf u v).map f).sum


end Shuffle

section Field
variable [Field K] [CharZero K]

/-- The exponential `exp(ℓ)` of the plane `ℓ = Σ_x c_x x`, as a function on words:
its coefficient at `w` is `c_{x_1} ⋯ c_{x_n} / n!`. -/
def expPlane (c : X → K) : List X → K := fun w => (w.map c).prod / (Nat.factorial w.length)



end Field

/-! ## Divided powers: the one-letter case of Ree's theorem -/



end FreeMonoidShuffle


