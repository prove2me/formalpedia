-- Prove2me | Definitions.Def_Novelty_FreeMonoidShuffle
-- name    : Novelty_FreeMonoidShuffle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:13:02.273436+00:00
-- url     : https://prove2.me/theorems/7d44337c-ec47-44fe-a3ae-d478068202bf
-- title:
--   Aether Catalog definitions — Novelty_FreeMonoidShuffle
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FreeMonoidShuffle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FreeMonoidShuffle.lean by skeleton subtraction
import Mathlib
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

namespace FreeMonoidShuffle

variable {X : Type*}

/-! ## The shuffle product of two words -/

/-- The multiset of all shuffles (interleavings, with multiplicity) of two words. -/
def shuf : List X → List X → Multiset (List X)
  | [], v => {v}
  | u, [] => {u}
  | a :: u, b :: v =>
      ((shuf u (b :: v)).map (a :: ·)) + ((shuf (a :: u) v).map (b :: ·))
  termination_by u v => u.length + v.length







/-! ## The bilinear extension of the shuffle product -/

/-- Shuffling a whole multiset of words with a fixed word. -/
def bindShuf (s : Multiset (List X)) (w : List X) : Multiset (List X) :=
  s.bind (fun z => shuf z w)








end FreeMonoidShuffle


