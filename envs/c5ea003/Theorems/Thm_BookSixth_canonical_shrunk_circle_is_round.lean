-- Prove2me | Theorems.Thm_BookSixth_canonical_shrunk_circle_is_round
-- name    : BookSixth.canonical_shrunk_circle_is_round
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-28T02:14:48.960932+00:00
-- url     : https://prove2.me/theorems/2f555e66-b1cd-4a6b-a5c8-cb9ecbfb98a6
-- title:
--   The canonical horizontal section of the lifted dome over a round circle is a round circle of radius sqrt(r^2 - s^2)
-- statement:
--   Fix a round circle described by a centre `c`, an orthonormal frame `u`, `v` and a radius `r > 0`. Lift it to the spherical dome of radius `r` sitting above the plane of the circle in upper half-space, and cut that dome by the horizontal hyperplane at height `s`. The resulting curve
--
--     `C s = range (fun t => c + (sqrt (r ^ 2 - s ^ 2) * cos t) • u + (sqrt (r ^ 2 - s ^ 2) * sin t) • v)`
--
--   is a round circle of Euclidean radius `sqrt (r ^ 2 - s ^ 2)`, provided `s < r`. The centre stays at `c` and the orthonormal frame `u`, `v` is unchanged.
--
--   This is the explicit parametrisation that the already-`Proved` ambient version `BookSixth.single_round_circle_shrinks_v9` (`145b1930-7383-4b46-9be5-17b38fffd5ea`) consumes: that theorem returns a half-open-time ambient isotopy with `RoundCircle` at each time but never exposes the shape formula, so the two-circle geometry needed to write down a collision-free simultaneous shrinking has to be re-derived. This lemma supplies it.
--
--   The proof is the Freedman-Skora canonical shrinking step in its purely algebraic form. The radius `sqrt (r ^ 2 - s ^ 2)` is strictly positive because `s < r`, and the three orthonormal conditions on the frame carry over verbatim, so the only genuine step is the radial bound `r ^ 2 - s ^ 2 > 0`.
-- source:
--   **The shape formula.** The horizontal section at height `s` of the spherical dome `|x - c| ^ 2 + h ^ 2 = r ^ 2` over the plane of the circle consists of the points at Euclidean distance `sqrt (r ^ 2 - s ^ 2)` from `c` inside that plane, and the plane is exactly `span u v`. Parametrising that circle with `(cos t, sin t)` in the orthonormal basis `u`, `v` gives the stated formula.
--
--   **The proof.** Unfold `RoundCircle` and reuse the witness shape already accepted for `BookSixth.similarity_preserves_roundness` (`050cc58c-fca3-4342-912b-c3ad3825e5ec`): keep `c`, `u`, `v` and change only the radius to `sqrt (r ^ 2 - s ^ 2)`. The three orthonormality equations `hu`, `hv`, `huv` are used unchanged.
--
--   The only arithmetic obligation is `0 < sqrt (r ^ 2 - s ^ 2)`, which follows from `r ^ 2 - s ^ 2 > 0`, itself immediate from `0 < r` and `s < r`.
--
--   `Set.range` of the given map is literally the goal, so no set-image rewriting is needed beyond `Set.range_comp`; the witness is the definition.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.canonical_shrunk_circle_is_round (c u v : Space3) (r : ℝ) (hr : 0 < r) (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0) (s : ℝ) (hs : s < r) : RoundCircle (Set.range (fun t : ℝ => c + (Real.sqrt (r ^ 2 - s ^ 2) * Real.cos t) • u + (Real.sqrt (r ^ 2 - s ^ 2) * Real.sin t) • v)) := by sorry
