-- Prove2me | solution 1 for Catalog.Novelty.EmotionalChromaticNumber.emoChrom_colorable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:34:45.479477+00:00
-- url     : https://prove2.me/submissions/14ed2643-6c16-4bf8-8df3-e92768dc50e3

import Mathlib
import Definitions.Def_Geometry_EmotionalChromaticNumber

open Catalog.Novelty.EmotionalChromaticNumber SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

theorem solution (G : SimpleGraph V) : G.Colorable (emoChrom G) := by
  classical
  let S : Set ℕ := {k | 3 ≤ k ∧ G.Colorable k}
  have hne : S.Nonempty := by
    refine ⟨max (Fintype.card V) 3, le_max_right _ _, ?_⟩
    exact (SimpleGraph.colorable_of_fintype G).mono (le_max_left _ _)
  have hmem : emoChrom G ∈ S := by
    simpa [emoChrom, S] using Nat.sInf_mem hne
  exact hmem.2
