-- Prove2me | solution 1 for ShuffleOfSeries.shuffleSeries_counit_left
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T02:29:46.762365+00:00
-- url     : https://prove2.me/submissions/65fd767f-ce67-4917-8ad1-15751afcf24e

import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Definitions.Def_Novelty_FreeMonoidCharacters
import Definitions.Def_Novelty_RepresentativeFunctions
import Definitions.Def_Novelty_ShuffleOfSeries

open ShuffleOfSeries FreeMonoidShuffle

open ShuffleOfSeries FreeMonoidShuffle in
/-- **The counit is a left unit for the shuffle product of series.** -/
theorem solution {X K : Type*} [Field K] (f : List X → K) :
    shuffleSeries counit f = f := by
  funext w
  induction w generalizing f with
  | nil => simp [shuffleSeries, unsh, counit]
  | cons a w ih =>
      have h := ih (fun x => f (a :: x))
      simp only [shuffleSeries] at h ⊢
      rw [unsh, Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_map]
      simp only [Function.comp_def, counit, zero_mul, Multiset.map_const', Multiset.sum_replicate,
        smul_zero, zero_add]
      exact h
