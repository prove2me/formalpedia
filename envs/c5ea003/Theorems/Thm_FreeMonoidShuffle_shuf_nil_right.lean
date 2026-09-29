-- Prove2me | Theorems.Thm_FreeMonoidShuffle_shuf_nil_right
-- name    : FreeMonoidShuffle.shuf_nil_right
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:49:53.380026+00:00
-- url     : https://prove2.me/theorems/1d99de68-8d1c-4fa8-91e4-76c14735c29e
-- title:
--   Shuf nil right
-- statement:
--   Formal statement of `FreeMonoidShuffle.shuf_nil_right` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FreeMonoidShuffle.shuf_nil_right(u : List X) : shuf u ([] : List X) = {u} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FreeMonoidShuffle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FreeMonoidShuffle.lean#L36

-- Thm stub generated from Novelty/FreeMonoidShuffle.lean
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



@[simp]

theorem FreeMonoidShuffle.shuf_nil_right(u : List X) : shuf u ([] : List X) = {u} := by sorry
