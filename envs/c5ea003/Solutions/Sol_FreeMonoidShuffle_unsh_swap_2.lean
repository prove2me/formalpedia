-- Prove2me | solution 2 for FreeMonoidShuffle.unsh_swap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T00:51:23.96193+00:00
-- url     : https://prove2.me/submissions/7154b558-f391-4324-8585-da088fa82b71

import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle

open FreeMonoidShuffle

open FreeMonoidShuffle in
/-- **Cocommutativity of the unshuffle coproduct**: swapping the two halves of every
unshuffle of `w` gives back the same multiset. -/
theorem solution {X : Type*} [DecidableEq X] (w : List X) : (unsh w).map Prod.swap = unsh w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [unsh, Multiset.map_add, Multiset.map_map, Multiset.map_map]
      have e1 : (unsh w).map (Prod.swap ∘ fun p : List X × List X => (a :: p.1, p.2))
              = (unsh w).map (fun p : List X × List X => (p.1, a :: p.2)) := by
        conv_rhs => rw [← ih]
        rw [Multiset.map_map]
        rfl
      have e2 : (unsh w).map (Prod.swap ∘ fun p : List X × List X => (p.1, a :: p.2))
              = (unsh w).map (fun p : List X × List X => (a :: p.1, p.2)) := by
        conv_rhs => rw [← ih]
        rw [Multiset.map_map]
        rfl
      rw [e1, e2, add_comm]
