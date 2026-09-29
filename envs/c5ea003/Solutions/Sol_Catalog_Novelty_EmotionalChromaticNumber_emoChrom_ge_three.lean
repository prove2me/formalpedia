-- Prove2me | solution 1 for Catalog.Novelty.EmotionalChromaticNumber.emoChrom_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:25:03.15934+00:00
-- url     : https://prove2.me/submissions/d8066099-9a8f-457c-b05f-c8c29cbed706

import Mathlib
import Definitions.Def_Geometry_EmotionalChromaticNumber
open Catalog.Novelty.EmotionalChromaticNumber in
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) :
    3 ≤ emoChrom G := by
  unfold emoChrom
  apply le_csInf
  · -- `max 3 |V|` colours always suffice
    exact ⟨max 3 (Fintype.card V), le_max_left _ _,
      G.colorable_of_fintype.mono (le_max_right _ _)⟩
  · rintro k ⟨hk, -⟩
    exact hk
