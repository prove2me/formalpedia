-- Prove2me | Theorems.Thm_Catalog_Geometry_Peel_bodyLayer_volume
-- name    : Catalog.Geometry.Peel.bodyLayer_volume
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:06:25.21358+00:00
-- url     : https://prove2.me/theorems/7b3d576a-c35b-4fd8-af6a-c209ebe3a742
-- title:
--   The layer really has measure `vol K / N`.
-- statement:
--   **The layer really has measure `vol K / N`.**  For a measurable
--   star-shaped body of finite measure, the set-theoretic layer
--   `c_k • K \ c_{k+1} • K` has measure exactly `vol K / N`.
--
--   ```lean
--   theorem Catalog.Geometry.Peel.bodyLayer_volume(d N k : ℕ) (hd : 0 < d) (hN : 0 < N) (hk : k < N)
--       {K : Set (EuclideanSpace ℝ (Fin d))} (hmeas : MeasurableSet K) (hfin : volume K ≠ ⊤)
--       (hstar : StarShaped K) :
--       (volume (bodyLayer d K N k)).toReal = bodyVol d K / N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PeelDilationBodies.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PeelDilationBodies.lean#L161

-- Thm stub generated from Geometry/PeelDilationBodies.lean
import Mathlib
import Definitions.Def_Geometry_PeelDilationBodies
/-
# Cycle 3: universality of the matching family

The shell peeling of a Euclidean ball saturates the peeling bound, and the
`O(d)`-action on its layers exhibits the symmetry responsible for that
saturation.  A natural criticism is that this could be an artefact of the
ball: the ball is the most symmetric body there is, so of course it produces a
symmetric peeling.

This file removes that objection: the construction is *universal*.  For **any**
star-shaped body `K ⊆ ℝ^d` of finite measure the dilates
`c_k • K`, `c_k = (1 - k/N)^{1/d}`, peel `K` into `N` pieces of equal measure
`vol K / N` (`bodyPeel_gap`, `bodyLayer_volume`), and every layer is invariant
under the *entire* linear symmetry group of `K` (`bodyLayer_equivariant`).
Conversely, a dilation peeling all of whose layers have measure at most
`vol K / N` must be this one (`body_peel_rigidity`).  The ball family of the
previous file is the special case `K = B(0,1)`, where the symmetry group is
`O(d)`.

The upshot for the original question — a matching family of actions for the
peeling upper bound — is that the extremisers are parameterised by *all* pairs
`(K, G)` with `G` a group of linear symmetries of `K`: the dimension `d` fixes
the radial profile `(1 - k/N)^{1/d}`, and the body `K` is otherwise free.

## Lab notes

Cross-check in `d = 2` with `K` the unit square `[-1,1]^2` (`vol K = 4`) and
`N = 4`: dilation factors `1, √(3)/2, √(2)/2, 1/2, 0`, layer areas
`4·(1/4) = 1` each — identical factors to the disc case, as the theory
predicts: the factors depend only on `d` and `N`, never on `K`.
-/

open Catalog.Geometry.Peel

open Finset MeasureTheory Metric Pointwise

/-! ## Volumes of dilates -/





/-! ## Star-shaped bodies and nested dilates -/



/-! ## The universal equal-volume dilation peeling -/

theorem Catalog.Geometry.Peel.bodyLayer_volume(d N k : ℕ) (hd : 0 < d) (hN : 0 < N) (hk : k < N)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hmeas : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hstar : StarShaped K) :
    (volume (bodyLayer d K N k)).toReal = bodyVol d K / N := by sorry
