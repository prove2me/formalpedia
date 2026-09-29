-- Prove2me | solution 1 for AlmostLossless.card_correct_le_card_code
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T12:49:49.656511+00:00
-- url     : https://prove2.me/submissions/d5ea5394-a86e-46bd-b339-f2f24a92ab3a

import Definitions.Def_Logic_AlmostLossless_Core
open AlmostLossless in
theorem solution {S : Type*} {C : Type*} [Fintype S] [DecidableEq S] [Fintype C]
    (K : Code S C) : ({s | Correct K s} : Finset S).card ≤ Fintype.card C := by
  have hinj : Set.InjOn K.enc ({s | Correct K s} : Finset S) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Correct] at hx hy
    have : some x = some y := by rw [← hx, ← hy, hxy]
    exact Option.some.inj this
  have := Finset.card_le_card_of_injOn K.enc (fun x _ => Finset.mem_univ (K.enc x)) hinj
  simpa using this
