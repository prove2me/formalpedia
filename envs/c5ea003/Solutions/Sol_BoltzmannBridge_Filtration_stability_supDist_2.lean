-- Prove2me | solution 2 for BoltzmannBridge.Filtration.stability_supDist
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:35:45.773159+00:00
-- url     : https://prove2.me/submissions/137b3979-e7c2-4dc2-99cf-023fe75bddcd

import Mathlib
import Definitions.Def_Applications_BoltzmannBridge_BottleneckStability
import Definitions.Def_Applications_BoltzmannBridge_HigherPersistence
open Finset BigOperators BoltzmannBridge BoltzmannBridge.Filtration in
theorem solution {α : Type*} (F G : Filtration α) {D : ℝ}
    (hD : 0 ≤ D) (h : WeightCloseBy F G D) : Interleaved F G D := by
  refine ⟨hD, fun t σ hσ => ?_, fun t σ hσ => ?_⟩
  · -- `G.weight σ ≤ F.weight σ + D ≤ t + D`
    have hw : F.weight σ ≤ t := hσ
    have := (abs_le.1 (h σ)).1
    show G.weight σ ≤ t + D
    linarith
  · have hw : G.weight σ ≤ t := hσ
    have := (abs_le.1 (h σ)).2
    show F.weight σ ≤ t + D
    linarith
