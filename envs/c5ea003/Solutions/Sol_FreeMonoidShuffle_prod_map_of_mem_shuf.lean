-- Prove2me | solution 1 for FreeMonoidShuffle.prod_map_of_mem_shuf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:11:09.123461+00:00
-- url     : https://prove2.me/submissions/58400ac8-37f2-48b8-b01b-c84d2d346643

-- Thm stub generated from Novelty/FreeMonoidCharacters.lean
import Mathlib
import Definitions.Def_Novelty_FreeMonoidCharacters
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

open FreeMonoidShuffle

variable {X : Type*} {K : Type*}

/-! ## The counit -/




variable [CommRing K]

/-! ## Characters of the concatenation bialgebra -/








/-! ## Infinitesimal characters of the concatenation bialgebra -/





/-! ## Characters of the shuffle algebra -/

variable [CommRing K]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FMS

theorem shuf_nil_left (v : List X) : shuf ([] : List X) v = {v} := by
  rw [shuf]

theorem shuf_nil_right (u : List X) : shuf u ([] : List X) = {u} := by
  cases u with
  | nil => rw [shuf]
  | cons a u =>
    rw [shuf]
    simp

theorem shuf_cons (a : X) (u : List X) (b : X) (v : List X) :
    shuf (a :: u) (b :: v)
      = ((shuf u (b :: v)).map (a :: ·)) + ((shuf (a :: u) v).map (b :: ·)) := by
  rw [shuf]

theorem prod_map_of_mem_shuf {K : Type*} [CommMonoid K] (c : X → K) (u : List X) :
    ∀ (v z : List X), z ∈ shuf u v → (z.map c).prod = (u.map c).prod * (v.map c).prod := by
  induction u with
  | nil =>
    intro v z hz
    rw [shuf_nil_left, Multiset.mem_singleton] at hz
    subst hz; simp
  | cons a u ihu =>
    intro v
    induction v with
    | nil =>
      intro z hz
      rw [shuf_nil_right, Multiset.mem_singleton] at hz
      subst hz; simp
    | cons b v ihv =>
      intro z hz
      rw [shuf_cons] at hz
      rcases Multiset.mem_add.1 hz with h | h
      · obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.1 h
        have hp := ihu (b :: v) z' hz'
        simp only [List.map_cons, List.prod_cons, hp]
        simp [mul_assoc, mul_comm, mul_left_comm]
      · obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.1 h
        have hp := ihv z' hz'
        simp only [List.map_cons, List.prod_cons, hp]
        simp [mul_assoc, mul_comm, mul_left_comm]

/-! ### Infinitesimal characters of the concatenation bialgebra are the planes -/

end FMS

theorem solution (c : X → K) {u v z : List X} (hz : z ∈ shuf u v) :
    (z.map c).prod = (u.map c).prod * (v.map c).prod :=
  FMS.prod_map_of_mem_shuf c u v z hz
