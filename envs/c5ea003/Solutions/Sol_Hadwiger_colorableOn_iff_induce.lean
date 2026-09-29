-- Prove2me | solution 1 for Hadwiger.colorableOn_iff_induce
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:31:50.040345+00:00
-- url     : https://prove2.me/submissions/ed4cbef1-cb11-4def-8fc6-d25042d5416c

import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerCriticalEquiv

open Hadwiger SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

theorem solution [Fintype V] [DecidableEq V] {S : Finset V} (hk : 0 < k) :
    ColorableOn G S k ↔ (G.induce (↑S : Set V)).Colorable k := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Coloring.mk (fun x : {v // v ∈ (↑S : Set V)} => c x.1) ?_⟩
    intro x y hxy
    exact hc x.1 x.2 y.1 y.2 hxy
  · rintro ⟨C⟩
    refine ⟨fun v => if hv : v ∈ S then C ⟨v, hv⟩ else ⟨0, hk⟩, ?_⟩
    intro x hx y hy hxy
    have hne : C ⟨x, hx⟩ ≠ C ⟨y, hy⟩ := C.valid hxy
    simpa [hx, hy] using hne
