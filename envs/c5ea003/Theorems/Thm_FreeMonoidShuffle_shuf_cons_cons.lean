-- Prove2me | Theorems.Thm_FreeMonoidShuffle_shuf_cons_cons
-- name    : FreeMonoidShuffle.shuf_cons_cons
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:49:46.980721+00:00
-- url     : https://prove2.me/theorems/f28a7672-4783-4692-8224-b78c584a9951
-- title:
--   Shuf cons cons
-- statement:
--   Formal statement of `FreeMonoidShuffle.shuf_cons_cons` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FreeMonoidShuffle.shuf_cons_cons(a b : X) (u v : List X) :
--       shuf (a :: u) (b :: v) =
--         ((shuf u (b :: v)).map (a :: ·)) + ((shuf (a :: u) v).map (b :: ·)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FreeMonoidShuffle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FreeMonoidShuffle.lean#L41

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

theorem FreeMonoidShuffle.shuf_cons_cons(a b : X) (u v : List X) :
    shuf (a :: u) (b :: v) =
      ((shuf u (b :: v)).map (a :: ·)) + ((shuf (a :: u) v).map (b :: ·)) := by sorry
