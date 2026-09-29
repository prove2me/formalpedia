-- Prove2me | solution 1 for FreeMonoidShuffle.shuf_nil_left
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:59:08.686782+00:00
-- url     : https://prove2.me/submissions/c36b7fd3-bd84-46fe-ab74-529745c6f868

-- Sol generated from Novelty/FreeMonoidShuffle.lean
import Mathlib
import Definitions.Def_Novelty_FreeMonoidShuffle
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
@[simp] theorem solution(v : List X) : shuf ([] : List X) v = {v} := by rw [shuf]
