-- Prove2me | solution 1 for BookSixth.canonical_shrunk_circle_is_round_nonneg_height
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T03:01:52.822623+00:00
-- url     : https://prove2.me/submissions/9bac89ac-6031-4a97-a920-f6f15f06b77d

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

/-- **The canonical shrunk circle is round, for a non-negative cutting height.**

Cut the lifted spherical dome of radius `r` over the plane of a round circle by the
horizontal hyperplane at height `s`, where `0 ≤ s < r`. The section is the round
circle of radius `sqrt (r ^ 2 - s ^ 2)` with the same centre and the same
orthonormal frame.

This is the explicit parametrisation consumed by the already-`Proved` ambient
version `BookSixth.single_round_circle_shrinks_v9`: that theorem gives an isotopy of
round circles but never exhibits the shape, so the two-circle geometry of a
collision-free simultaneous shrinking has to recover it. The witness is the pattern
accepted for `BookSixth.similarity_preserves_roundness` — the centre and the
orthonormal frame are reused verbatim and only the radius changes. Hence the sole
arithmetic step is `0 < sqrt (r ^ 2 - s ^ 2)`.

The hypothesis `0 ≤ s` is what the sibling target
`BookSixth.canonical_shrunk_circle_is_round` (`2f555e66`) omits. That statement
assumes only `s < r`, which does not force `r ^ 2 - s ^ 2 > 0`; with `r = 1` and
`s = -1` every one of its hypotheses holds while the displayed set collapses to the
singleton `{c}`, which is not a round circle. Here `s` is a height in upper
half-space and is non-negative by construction. -/
theorem solution (c u v : Space3) (r : ℝ) (hr : 0 < r)
    (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1)
    (huv : (∑ i, u i * v i) = 0) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < r) :
    RoundCircle (Set.range
      (fun t : ℝ => c + (Real.sqrt (r ^ 2 - s ^ 2) * Real.cos t) • u
        + (Real.sqrt (r ^ 2 - s ^ 2) * Real.sin t) • v)) := by
  -- `0 ≤ s < r` with `0 < r` puts `s` strictly inside `(-r, r)`, so the radicand
  -- is a product of two strictly positive factors.
  have hdiff : 0 < r - s := by linarith
  have hsum : 0 < r + s := by linarith
  have hsq : 0 < (r - s) * (r + s) := mul_pos hdiff hsum
  have hpos : 0 < Real.sqrt (r ^ 2 - s ^ 2) := Real.sqrt_pos.2 (by nlinarith [hsq])
  refine ⟨c, u, v, Real.sqrt (r ^ 2 - s ^ 2), hpos, hu, hv, huv, rfl⟩
