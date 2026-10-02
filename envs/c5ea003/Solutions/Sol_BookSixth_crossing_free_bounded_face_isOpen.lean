-- Prove2me | solution 1 for BookSixth.crossing_free_bounded_face_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T06:51:34.965007+00:00
-- url     : https://prove2.me/submissions/11913a57-3107-4574-b747-ef9a024e369d

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthCrossingFreeFaceData
import Theorems.Thm_BookSixth_crossing_free_support_compact

open BookSixth

theorem solution {N M : ℕ}
    (D : PlaneDrawing N M)
    (V : Finset (Fin N))
    (E : Finset (Fin M))
    {U : Set CrossingFreePlane}
    (hU : U ∈ crossingFreeBoundedFaces D V E) :
    IsOpen U := by
  change Bornology.IsBounded U ∧
    ∃ x ∈ (crossingFreeSupport D V E)ᶜ,
      U = connectedComponentIn (crossingFreeSupport D V E)ᶜ x at hU
  rcases hU with ⟨_, x, hx, hcomponent⟩
  have hcompact : IsCompact (crossingFreeSupport D V E) :=
    crossing_free_support_compact D V E
  have hclosed : IsClosed (crossingFreeSupport D V E) :=
    hcompact.isClosed
  have hopen : IsOpen (crossingFreeSupport D V E)ᶜ :=
    hclosed.isOpen_compl
  rw [hcomponent]
  exact hopen.connectedComponentIn
