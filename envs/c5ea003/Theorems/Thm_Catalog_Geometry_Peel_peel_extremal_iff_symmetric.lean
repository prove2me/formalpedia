-- Prove2me | Theorems.Thm_Catalog_Geometry_Peel_peel_extremal_iff_symmetric
-- name    : Catalog.Geometry.Peel.peel_extremal_iff_symmetric
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:07:43.148592+00:00
-- url     : https://prove2.me/theorems/c7a87f8d-0412-40d7-8eb9-ce16a1fb207b
-- title:
--   Saturation is maximal symmetry.
-- statement:
--   **Saturation is maximal symmetry.**  The pigeonhole bound is saturated at
--   every step of the window if and only if the layer contents are invariant under
--   the full symmetric group acting on the window.
--
--   ```lean
--   theorem Catalog.Geometry.Peel.peel_extremal_iff_symmetric(hN : 0 < N) :
--       (∀ k < N, peelGap P k ≤ peelRate P N) ↔
--         ∀ (σ : Equiv.Perm (Fin N)) (i : Fin N), gapFin P N (σ • i) = gapFin P N i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PeelStabilityConcentration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PeelStabilityConcentration.lean#L97

-- Thm stub generated from Geometry/PeelStabilityConcentration.lean
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
import Definitions.Def_Geometry_PeelSymmetryConstruction
/-
# Cycle 2: stability of the peeling bound, and boundary concentration

The first two files of this thread proved the peeling upper bound
(`exists_peel_stopping_time`, `peelEstimate_error`), its rigidity
(`peel_extremal_tfae`) and produced the matching `O(d)`-equivariant family of
equal-volume shell peelings of a Euclidean ball.  Rigidity is an all-or-nothing
statement: *exact* saturation forces the arithmetic profile.  This file closes
the two gaps that criticism of that statement immediately exposes.

1. **Stability.**  `peel_stability`: if every layer is at most `(1 + ε)` times
   the average rate — an approximate extremiser — then the profile is
   uniformly within `ε · budget` of the arithmetic one.  At `ε = 0` this
   recovers rigidity, and the bound is linear in `ε`, so approximate
   extremisers are approximately arithmetic.  The geometric consequence for
   ball peelings is `ball_peel_stability`.

2. **Maximal symmetry.**  `peel_extremal_iff_symmetric`: saturation of the
   pigeonhole bound is *equivalent* to invariance of the layer contents under
   the full symmetric group of the window.  Combined with
   `peel_extremal_of_cyclic_action` this shows that a single `N`-cycle already
   buys the whole symmetric group's worth of information.

3. **When no search is needed.**  `peel_last_gap_le_rate_of_antitone_gap`: for
   peelings with decreasing layer contents the last step of the window is
   always an admissible stopping time, and the first step is always
   inadmissible.  The existential in `exists_peel_stopping_time` is therefore
   only needed for genuinely oscillating peelings.

4. **Boundary concentration.**  `shell_thickness_le`: in the equal-volume
   shell peeling of `B(0,R) ⊆ ℝ^d`, the outermost shell carries a `1/N`
   fraction of the volume but has thickness at most `R / (d (N-1))`.  The
   discrepancy factor is exactly the dimension: equal-volume peelings of
   high-dimensional balls collapse onto the boundary sphere.  This is the
   quantitative reason ball peelings behave so differently from the abstract
   arithmetic profile they realise.

## Lab notes

`d = 10`, `N = 2`, `R = 1`: outer shell thickness `1 - 2^{-1/10} ≈ 0.0670`,
bound `1/(d(N-1)) = 0.1`; `d = 100`, `N = 2`: thickness `≈ 0.0069`, bound
`0.01`.  The bound is within roughly `30 %` of the truth in these ranges and
has the correct `1/d` decay, which is what the proof through the factorisation
`1 - s^d = (1-s)(1 + s + ... + s^{d-1})` is designed to capture.
-/

open Catalog.Geometry.Peel

open Finset MeasureTheory Metric

variable (P : PeelProfile) {N k : ℕ}

/-! ## Stability of the peeling bound -/


/-! ## Maximal symmetry characterises the extremisers -/

theorem Catalog.Geometry.Peel.peel_extremal_iff_symmetric(hN : 0 < N) :
    (∀ k < N, peelGap P k ≤ peelRate P N) ↔
      ∀ (σ : Equiv.Perm (Fin N)) (i : Fin N), gapFin P N (σ • i) = gapFin P N i := by sorry
