-- Prove2me | solution 1 for FreeMonoidShuffle.shuf_assoc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:08:16.34165+00:00
-- url     : https://prove2.me/submissions/1cbb20fe-2ae9-4ebc-add6-b73d9dd88d49

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





/-- The shuffle product is commutative. -/
theorem shuf_comm (u v : List X) : shuf u v = shuf v u := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    induction v with
    | nil => simp
    | cons b v ihv => rw [shuf_cons_cons, shuf_cons_cons, ih (b :: v), ihv]; exact add_comm _ _



/-! ## The bilinear extension of the shuffle product -/


@[simp] lemma bindShuf_singleton (u w : List X) : bindShuf {u} w = shuf u w := by simp [bindShuf]

@[simp] lemma bindShuf_add (s t : Multiset (List X)) (w : List X) :
    bindShuf (s + t) w = bindShuf s w + bindShuf t w := by simp [bindShuf, Multiset.add_bind]


@[simp] lemma bindShuf_nil (s : Multiset (List X)) : bindShuf s [] = s := by
  simp only [bindShuf, shuf_nil_right]
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [ih]

lemma bindShuf_map_cons (a c : X) (t : Multiset (List X)) (w : List X) :
    bindShuf (t.map (a :: ·)) (c :: w) =
      (bindShuf t (c :: w)).map (a :: ·) + (bindShuf (t.map (a :: ·)) w).map (c :: ·) := by
  simp only [bindShuf, Multiset.bind_map, Multiset.map_bind]
  rw [← Multiset.bind_add]
  exact Multiset.bind_congr (fun z _ => shuf_cons_cons a c z w)




open FreeMonoidShuffle in
theorem solution(u v w : List X) : bindShuf (shuf u v) w = bindShuf (shuf v w) u := by
  induction hn : u.length + v.length + w.length using Nat.strong_induction_on
    generalizing u v w with
  | _ n ih =>
  match u, v, w with
  | [], v, w => simp
  | u, [], w => simp [shuf_comm]
  | u, v, [] => simp [shuf_comm]
  | a :: u, b :: v, c :: w =>
    subst hn
    rw [shuf_cons_cons a b u v, shuf_cons_cons b c v w]
    rw [bindShuf_add, bindShuf_add, bindShuf_map_cons, bindShuf_map_cons,
        bindShuf_map_cons, bindShuf_map_cons]
    have e1 : bindShuf (shuf u (b :: v)) (c :: w) = bindShuf (shuf (b :: v) (c :: w)) u :=
      ih _ (by simp) u (b :: v) (c :: w) rfl
    have e2 : bindShuf (shuf (a :: u) v) (c :: w) = bindShuf (shuf v (c :: w)) (a :: u) :=
      ih _ (by simp) (a :: u) v (c :: w) rfl
    have e3 : bindShuf (shuf (a :: u) (b :: v)) w = bindShuf (shuf (b :: v) w) (a :: u) :=
      ih _ (by simp) (a :: u) (b :: v) w rfl
    have hA : (bindShuf (shuf (b :: v) (c :: w)) u).map (a :: ·) =
        (bindShuf ((shuf v (c :: w)).map (b :: ·)) u).map (a :: ·) +
        (bindShuf ((shuf (b :: v) w).map (c :: ·)) u).map (a :: ·) := by
      rw [shuf_cons_cons b c v w, bindShuf_add, Multiset.map_add]
    have hC : (bindShuf (shuf (b :: v) w) (a :: u)).map (c :: ·) =
        (bindShuf ((shuf u (b :: v)).map (a :: ·)) w).map (c :: ·) +
        (bindShuf ((shuf (a :: u) v).map (b :: ·)) w).map (c :: ·) := by
      rw [← e3, shuf_cons_cons a b u v, bindShuf_add, Multiset.map_add]
    rw [e1, e2, hA, hC]
    abel
