-- Prove2me | solution 1 for FreeMonoidShuffle.shuffleCharacter_pow_letter
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:08:17.067604+00:00
-- url     : https://prove2.me/submissions/5b6d6c5b-f726-4adc-916d-d9d8f89f7070

-- Sol generated from Novelty/FreeMonoidCharacters.lean
import Mathlib
import Definitions.Def_Novelty_FreeMonoidCharacters
import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Theorems.Thm_FreeMonoidShuffle_shuf_cons_cons
import Theorems.Thm_FreeMonoidShuffle_shuf_nil_left
import Theorems.Thm_FreeMonoidShuffle_shuf_nil_right
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




variable [Field K] [CharZero K]





/-! ## Divided powers: the one-letter case of Ree's theorem -/

theorem shuf_replicate_letter {X : Type*} (a : X) (n : ℕ) :
    shuf (List.replicate n a) [a] = Multiset.replicate (n + 1) (List.replicate (n + 1) a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, shuf_cons_cons, ih, shuf_nil_right]
    simp only [Multiset.map_replicate, Multiset.map_singleton, ← List.replicate_succ]
    rw [Multiset.replicate_add (n + 1) 1]
    rfl



open FreeMonoidShuffle in
theorem solution{X : Type*} {K : Type*} [Field K] [CharZero K]
    {f : List X → K} (hf : IsShuffleCharacter f) (a : X) (n : ℕ) :
    f (List.replicate n a) = f [a] ^ n / (Nat.factorial n) := by
  induction n with
  | zero => simpa using hf.1
  | succ n ih =>
    have hfn : (Nat.factorial n : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hfn1 : (Nat.factorial (n + 1) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hfac : (Nat.factorial (n + 1) : K) = ((n : K) + 1) * (Nat.factorial n : K) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h := hf.2 (List.replicate n a) [a]
    rw [shuf_replicate_letter a n, Multiset.map_replicate, Multiset.sum_replicate,
      nsmul_eq_mul, ih] at h
    push_cast at h
    rw [div_mul_eq_mul_div, div_eq_iff hfn] at h
    rw [eq_div_iff hfn1, hfac]
    linear_combination -h
