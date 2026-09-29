-- Prove2me | solution 1 for Catalog.Novelty.EmotionalChromaticNumber.emoChrom_eq_three_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T07:05:52.067741+00:00
-- url     : https://prove2.me/submissions/e14336da-96cf-43e2-9772-ff1b4b5b0e59

import Mathlib
import Definitions.Def_Geometry_EmotionalChromaticNumber

open Catalog.Novelty.EmotionalChromaticNumber SimpleGraph
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

theorem solution (G : SimpleGraph V) :
    emoChrom G = 3 ↔ G.Colorable 3 := by
  classical
  let S : Set ℕ := {k | 3 ≤ k ∧ G.Colorable k}
  have hne : S.Nonempty := by
    refine ⟨max (Fintype.card V) 3, le_max_right _ _, ?_⟩
    exact (SimpleGraph.colorable_of_fintype G).mono (le_max_left _ _)
  have hmem : emoChrom G ∈ S := by
    simpa [emoChrom, S] using Nat.sInf_mem hne
  constructor
  · intro h
    simpa [h] using hmem.2
  · intro hc
    refine le_antisymm ?_ hmem.1
    exact Nat.sInf_le ⟨le_rfl, hc⟩
