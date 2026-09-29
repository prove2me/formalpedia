-- Prove2me | solution 1 for TimeTravelDeep.involution_fixedPoints_parity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:44:45.399794+00:00
-- url     : https://prove2.me/submissions/2f3285fb-d771-4e07-97b6-5f298c6e31ef

import Mathlib
import Definitions.Def_Logic_TimeTravelRecurrence
open Function in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] (f : S → S)
    (hf : Involutive f) :
    Fintype.card {s // f s = s} % 2 = Fintype.card S % 2 := by
  -- an involution is an element of order dividing `2 = 2^1` in `Function.End S`
  let F : Function.End S := f
  have hF2 : F ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    funext x
    show f (f x) = x
    exact hf x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hF2
  have hcard : Fintype.card {s // f s = s} = Fintype.card (Function.fixedPoints F) :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [hcard]
  exact hmod.symm
