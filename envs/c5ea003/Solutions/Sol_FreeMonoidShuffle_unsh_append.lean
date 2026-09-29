-- Prove2me | solution 1 for FreeMonoidShuffle.unsh_append
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T01:49:21.160106+00:00
-- url     : https://prove2.me/submissions/5b5b4926-cd45-4224-9305-409459f99832

import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle

open FreeMonoidShuffle

open FreeMonoidShuffle in
/-- **The unshuffle coproduct is multiplicative for concatenation.** -/
theorem solution {X : Type*} [DecidableEq X] (u v : List X) :
    unsh (u ++ v) = pairMul (unsh u) (unsh v) := by
  induction u with
  | nil => simp [unsh, pairMul]
  | cons a u ih =>
      simp only [List.cons_append, unsh, ih, pairMul, Multiset.add_bind, Multiset.bind_map,
        Multiset.map_bind, Multiset.map_map, Function.comp_def]
