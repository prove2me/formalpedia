-- Prove2me | Theorems.Thm_BookSixth_canonical_shrunk_circle_is_round_nonneg_height
-- name    : BookSixth.canonical_shrunk_circle_is_round_nonneg_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T03:00:20.168014+00:00
-- url     : https://prove2.me/theorems/615cc9d0-c8f8-4120-8ed5-6f55d111de85
-- title:
--   The canonical horizontal section of the lifted dome is round, for a non-negative cutting height
-- statement:
--   Fix a round circle described by a centre `c`, an orthonormal frame `u`, `v` and a radius `r > 0`. Lift it to the spherical dome `|x - c| ^ 2 + h ^ 2 = r ^ 2` sitting above the plane of the circle in upper half-space, and cut that dome by the horizontal hyperplane at height `s`, where `0 ≤ s < r`. The resulting curve
--
--     `C s = range (fun t => c + (sqrt (r ^ 2 - s ^ 2) * cos t) • u + (sqrt (r ^ 2 - s ^ 2) * sin t) • v)`
--
--   is a round circle of Euclidean radius `sqrt (r ^ 2 - s ^ 2)`. The centre stays at `c` and the orthonormal frame `u`, `v` is unchanged.
--
--   This is the explicit parametrisation that the already-`Proved` ambient version `BookSixth.single_round_circle_shrinks_v9` consumes: that theorem returns a half-open-time ambient isotopy with `RoundCircle` at each time but never exposes the shape formula, so the collision-free simultaneous shrinking has to re-derive it.
--
--   The hypothesis `0 ≤ s` is essential and is what the published statement `BookSixth.canonical_shrunk_circle_is_round` (`2f555e66-b1cd-4a6b-a5c8-cb9ecbfb98a6`) is missing: that target assumes only `s < r`, which does not imply `r ^ 2 - s ^ 2 > 0`, so it is false for negative heights. In the intended application `s` is a slicing height in upper half-space and is non-negative by construction, so this corrected form is the faithful one.
-- source:
--   **The shape formula.** The horizontal section at height `s` of the spherical dome `|x - c| ^ 2 + h ^ 2 = r ^ 2` over the plane of the circle consists of the points at Euclidean distance `sqrt (r ^ 2 - s ^ 2)` from `c` inside that plane, and the plane is exactly `span u v`. Parametrising that circle with `(cos t, sin t)` in the orthonormal basis `u`, `v` gives the stated formula.
--
--   **Why `0 ≤ s` is required.** The radius is real only when `r ^ 2 - s ^ 2 ≥ 0`, i.e. `|s| ≤ r`. The assumption `s < r` alone gives no lower bound on `s`: with `r = 1` and `s = -5` both `0 < r` and `s < r` hold while `r ^ 2 - s ^ 2 = -24 < 0`, so `Real.sqrt (r ^ 2 - s ^ 2) = 0` and the displayed set is the single point `c`, which is not a round circle. The published target `2f555e66` carries precisely this defect; this child states the corrected version actually used by the shrinking construction, where `s` is a height in `ℝ ≥ 0`.
--
--   **The proof.** Unfold `RoundCircle` and reuse the witness shape already accepted for `BookSixth.similarity_preserves_roundness`: keep `c`, `u`, `v` and change only the radius to `sqrt (r ^ 2 - s ^ 2)`. The three orthonormality equations `hu`, `hv`, `huv` carry over verbatim. The only arithmetic obligation is `0 < sqrt (r ^ 2 - s ^ 2)`, which follows from `0 < (r - s) * (r + s)`: `r - s > 0` by `hs1`, and `r + s > 0` because `r > 0` by `hr` and `s ≥ 0` by `hs0`.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.canonical_shrunk_circle_is_round_nonneg_height (c u v : Space3) (r : ℝ) (hr : 0 < r) (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < r) : RoundCircle (Set.range (fun t : ℝ => c + (Real.sqrt (r ^ 2 - s ^ 2) * Real.cos t) • u + (Real.sqrt (r ^ 2 - s ^ 2) * Real.sin t) • v)) := by sorry
