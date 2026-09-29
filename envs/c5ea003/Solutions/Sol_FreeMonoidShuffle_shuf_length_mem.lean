-- Prove2me | solution 1 for FreeMonoidShuffle.shuf_length_mem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:06:28.71582+00:00
-- url     : https://prove2.me/submissions/6999c1fd-2236-47e4-9a3f-8ede7c2c666a

-- Sol generated from Novelty/FreeMonoidShuffle.lean
import Mathlib
import Definitions.Def_Novelty_FreeMonoidShuffle
import Theorems.Thm_FreeMonoidShuffle_shuf_cons_cons
import Theorems.Thm_FreeMonoidShuffle_shuf_nil_left
import Theorems.Thm_FreeMonoidShuffle_shuf_nil_right
/-
# Shuffle products on a free monoid

This file develops, from scratch, the combinatorial core of the shuffle product on the
free monoid `List X = X*` over an alphabet `X`, in the multiset ("with multiplicities")
formulation.  This is the basic layer underlying the bialgebras of representative
functions on free monoids: the shuffle product `⧢`, the unshuffle (deconcatenation-dual)
coproduct, and their duality.

Main results:

* `shuf` : the multiset of shuffles of two words, defined by the classical recursion.
* `shuf_comm`, `shuf_assoc`, `shuf_nil_left/right` : `(Multiset (List X), shuf)` is a
  commutative monoid-like structure (associativity is stated through `bindShuf`, the
  bilinear extension of `shuf`).
* `shuf_card` : `|u ⧢ v| = C(|u|+|v|, |u|)`.
* `shuf_length_mem` : shuffles are length graded.
-/

open FreeMonoidShuffle

variable {X : Type*}

/-! ## The shuffle product of two words -/








/-! ## The bilinear extension of the shuffle product -/










open FreeMonoidShuffle in
theorem solution{u v z : List X} (hz : z ∈ shuf u v) :
    z.length = u.length + v.length := by
  induction hn : u.length + v.length using Nat.strong_induction_on generalizing u v z with
  | _ n ih =>
  match u, v with
  | [], v =>
    subst hn; rw [shuf_nil_left] at hz; simp only [Multiset.mem_singleton] at hz; simp [hz]
  | u, [] =>
    subst hn; rw [shuf_nil_right] at hz; simp only [Multiset.mem_singleton] at hz; simp [hz]
  | a :: u, b :: v =>
    subst hn
    rw [shuf_cons_cons] at hz
    rcases Multiset.mem_add.1 hz with h | h
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 h
      have := ih (u.length + (b :: v).length) (by simp) hy rfl
      simp [this]; omega
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 h
      have := ih ((a :: u).length + v.length) (by simp) hy rfl
      simp [this]; omega
