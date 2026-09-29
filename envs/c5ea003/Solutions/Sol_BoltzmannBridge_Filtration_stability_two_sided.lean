-- Prove2me | solution 1 for BoltzmannBridge.Filtration.stability_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:40:00.820106+00:00
-- url     : https://prove2.me/submissions/b82be9d0-f3fe-4aa3-a630-69054e344ea9

import Mathlib
import Definitions.Def_Applications_BoltzmannBridge_HigherPersistence
open Finset BigOperators BoltzmannBridge BoltzmannBridge.Filtration in
theorem solution {α : Type*} (F G : Filtration α) {δ : ℝ}
    (h : ∀ σ : Finset α, |F.weight σ - G.weight σ| ≤ δ) (t : ℝ) :
    F.sublevelFaces t ⊆ G.sublevelFaces (t + δ) ∧
    G.sublevelFaces t ⊆ F.sublevelFaces (t + δ) := by
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · -- `G.weight σ ≤ F.weight σ + δ ≤ t + δ`
    have hw : F.weight σ ≤ t := hσ
    have := (abs_le.1 (h σ)).1
    show G.weight σ ≤ t + δ
    linarith
  · have hw : G.weight σ ≤ t := hσ
    have := (abs_le.1 (h σ)).2
    show F.weight σ ≤ t + δ
    linarith
