-- Prove2me | solution 1 for BookSixth.crossing_free_support_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T23:06:56.81728+00:00
-- url     : https://prove2.me/submissions/184a165c-0987-46d7-9284-d38085252971

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthCrossingFreeFaceData

open BookSixth

theorem solution {N M : ℕ}
    (D : PlaneDrawing N M)
    (V : Finset (Fin N))
    (E : Finset (Fin M)) :
    IsCompact (crossingFreeSupport D V E) := by
  classical
  have hvertices : IsCompact (D.vertex '' (V : Set (Fin N))) := by
    simpa only [Finset.coe_image] using (V.image D.vertex).finite_toSet.isCompact
  have hedge : IsCompact (⋃ e ∈ E, Set.range (D.arc e)) := by
    apply Finset.isCompact_biUnion
    intro e he
    exact isCompact_range (D.continuous_arc e)
  have hsupport :
      (crossingFreeSupport D V E) =
        (D.vertex '' (V : Set (Fin N))) ∪ ⋃ e ∈ E, Set.range (D.arc e) := by
    ext x
    simp [crossingFreeSupport]
  rw [hsupport]
  exact hvertices.union hedge
