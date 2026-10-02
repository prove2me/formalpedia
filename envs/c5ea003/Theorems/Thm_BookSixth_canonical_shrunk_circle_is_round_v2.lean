-- Prove2me | Theorems.Thm_BookSixth_canonical_shrunk_circle_is_round_v2
-- name    : BookSixth.canonical_shrunk_circle_is_round_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T03:00:15.683725+00:00
-- url     : https://prove2.me/theorems/a7cd3564-fd88-4669-a58e-b5d53aee6aba
-- title:
--   The canonical horizontal section of the lifted dome over a round circle is a round circle of radius sqrt(r^2 - s^2)
-- statement:
--   Fix a round circle with centre `c`, orthonormal frame `u`, `v` and radius `r > 0`. Lift it to the spherical dome of radius `r` sitting above the plane of the circle in upper half-space, and cut that dome by the horizontal hyperplane at height `s`, where `0 ≤ s < r`. The resulting curve
--
--     `C s = range (fun t => c + (sqrt (r ^ 2 - s ^ 2) * cos t) • u + (sqrt (r ^ 2 - s ^ 2) * sin t) • v)`
--
--   is a round circle of Euclidean radius `sqrt (r ^ 2 - s ^ 2)`. The centre stays at `c` and the orthonormal frame `u`, `v` is unchanged.
--
--   This is the explicit parametrisation that the already-`Proved` ambient version `BookSixth.single_round_circle_shrinks_v9` (`145b1930-7383-4b46-9be5-17b38fffd5ea`) consumes: that theorem returns a half-open-time ambient isotopy with `RoundCircle` at each time but never exposes the shape formula, so the two-circle geometry needed to write down a collision-free simultaneous shrinking has to be re-derived. This lemma supplies it.
--
--   The restriction `0 ≤ s` is not cosmetic. Only for `0 ≤ s < r` does `r ^ 2 - s ^ 2` exceed zero; see the correction note below. Heights in the dome construction are non-negative by definition, so the strengthened hypothesis costs nothing.
-- source:
--   **The shape formula.** The horizontal section at height `s` of the spherical dome `|x - c| ^ 2 + h ^ 2 = r ^ 2` over the plane of the circle consists of the points at Euclidean distance `sqrt (r ^ 2 - s ^ 2)` from `c` inside that plane, and the plane is exactly `span u v`. Parametrising that circle with `(cos t, sin t)` in the orthonormal basis `u`, `v` gives the stated formula.
--
--   **The proof.** Unfold `RoundCircle` and reuse the witness shape already accepted for `BookSixth.similarity_preserves_roundness` (`050cc58c-fca3-4342-912b-c3ad3825e5ec`): keep `c`, `u`, `v` and change only the radius to `sqrt (r ^ 2 - s ^ 2)`. The three orthonormality equations `hu`, `hv`, `huv` are used unchanged, so the `Set.range` equation is `rfl`.
--
--   The only arithmetic step is `0 < sqrt (r ^ 2 - s ^ 2)`, from `r ^ 2 - s ^ 2 > 0`, immediate from `0 ≤ s < r`.
--
--   **Correction note.** The earlier catalogue entry `BookSixth.canonical_shrunk_circle_is_round` (`2f555e66-b1cd-4a6b-a5c8-cb9ecbfb98a6`) assumed only `s < r`. That is insufficient: with `r = 1` and `s = -1` the hypotheses `0 < r` and `s < r` both hold, but `r ^ 2 - s ^ 2 = 0`, so the claimed radius is `0` and the conclusion fails. Since dome heights satisfy `0 ≤ s` by construction, this `_v2` entry adds that hypothesis and is the correct statement.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.canonical_shrunk_circle_is_round_v2 (c u v : Space3) (r : ℝ) (hr : 0 < r) (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < r) : RoundCircle (Set.range (fun t : ℝ => c + (Real.sqrt (r ^ 2 - s ^ 2) * Real.cos t) • u + (Real.sqrt (r ^ 2 - s ^ 2) * Real.sin t) • v)) := by sorry
