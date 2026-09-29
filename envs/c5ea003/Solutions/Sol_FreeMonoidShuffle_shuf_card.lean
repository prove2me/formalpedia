-- Prove2me | solution 1 for FreeMonoidShuffle.shuf_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:06:28.125378+00:00
-- url     : https://prove2.me/submissions/d39facbe-93bd-471f-9f62-be902cab27ec

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
theorem solution(u v : List X) :
    (shuf u v).card = (u.length + v.length).choose u.length := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    induction v with
    | nil => simp
    | cons b v ihv =>
      rw [shuf_cons_cons]
      simp only [Multiset.card_add, Multiset.card_map, ih, ihv, List.length_cons]
      have h1 : u.length + (v.length + 1) = u.length + v.length + 1 := by omega
      have h2 : u.length + 1 + v.length = u.length + v.length + 1 := by omega
      have h3 : u.length + 1 + (v.length + 1) = (u.length + v.length + 1) + 1 := by omega
      rw [h1, h2, h3, Nat.choose_succ_succ' (u.length + v.length + 1) u.length]
