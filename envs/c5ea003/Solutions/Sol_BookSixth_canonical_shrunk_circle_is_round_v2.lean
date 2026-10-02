-- Prove2me | solution 1 for BookSixth.canonical_shrunk_circle_is_round_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T03:07:12.226041+00:00
-- url     : https://prove2.me/submissions/8f7ec19a-0b33-457c-bf5b-74557902bc0a

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

/-- **The canonical shrunk circle is round.**  Cut the lifted spherical dome of
radius `r` over the plane of a round circle by the horizontal hyperplane at height
`s`, where `0 ≤ s < r`.  The section is the round circle of radius
`sqrt (r ^ 2 - s ^ 2)` with the same centre and the same orthonormal frame.

This is the explicit parametrisation consumed by the already-`Proved` ambient version
`BookSixth.single_round_circle_shrinks_v9`: that theorem gives an isotopy of round
circles but never exhibits the shape, so the two-circle geometry of a collision-free
simultaneous shrinking has to recover it.  The witness is the pattern accepted for
`BookSixth.similarity_preserves_roundness` — the centre and the orthonormal frame are
reused verbatim and only the radius changes.  Hence the sole arithmetic step is
`0 < sqrt (r ^ 2 - s ^ 2)`.

The hypothesis `0 ≤ s` is needed: `s < r` alone does not give `r ^ 2 - s ^ 2 > 0`. -/
theorem solution (c u v : Space3) (r : ℝ) (hr : 0 < r)
    (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1)
    (huv : (∑ i, u i * v i) = 0) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < r) :
    RoundCircle (Set.range
      (fun t : ℝ => c + (Real.sqrt (r ^ 2 - s ^ 2) * Real.cos t) • u
        + (Real.sqrt (r ^ 2 - s ^ 2) * Real.sin t) • v)) := by
  have hsq : 0 < r ^ 2 - s ^ 2 := by nlinarith
  have hpos : 0 < Real.sqrt (r ^ 2 - s ^ 2) := Real.sqrt_pos.2 hsq
  refine ⟨c, u, v, Real.sqrt (r ^ 2 - s ^ 2), hpos, hu, hv, huv, rfl⟩
