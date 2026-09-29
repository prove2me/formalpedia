-- Prove2me | solution 1 for Hadwiger.colorable_induce_compl_of_colorableOn_erase
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T04:34:18.899983+00:00
-- url     : https://prove2.me/submissions/187f2ea0-cc1e-46fc-b552-8ecbf6ea8a83

import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerCriticalEquiv

open Hadwiger SimpleGraph Finset in
theorem solution {V : Type*} {G : SimpleGraph V} {k : ℕ} [Fintype V] [DecidableEq V]
    {S : Finset V} {x : (↑S : Set V)} (h : ColorableOn G (S.erase x.1) k) :
    (((G.induce (↑S : Set V)).induce ({x}ᶜ : Set (↑S : Set V)))).Colorable k := by
  obtain ⟨c, hc⟩ := h
  -- every vertex of the doubly induced graph is a vertex of `S` other than `x`
  have hmem : ∀ w : ({x}ᶜ : Set (↑S : Set V)), w.1.1 ∈ S.erase x.1 := by
    intro w
    rw [mem_erase]
    exact ⟨fun h => w.2 (Subtype.ext h), w.1.2⟩
  refine ⟨Coloring.mk (fun w => c w.1.1) ?_⟩
  intro w w' hadj
  exact hc _ (hmem w) _ (hmem w') hadj
