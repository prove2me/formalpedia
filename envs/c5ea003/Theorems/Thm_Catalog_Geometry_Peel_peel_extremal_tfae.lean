-- Prove2me | Theorems.Thm_Catalog_Geometry_Peel_peel_extremal_tfae
-- name    : Catalog.Geometry.Peel.peel_extremal_tfae
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:05:50.253744+00:00
-- url     : https://prove2.me/theorems/5b046f4d-50e1-4c8c-babd-2d5bcf68ffe0
-- title:
--   Rigidity of the peeling bound.
-- statement:
--   **Rigidity of the peeling bound.**  For a window of `N` steps the
--   following are equivalent:
--
--   1. every layer is at most the average rate;
--   2. every layer equals the average rate;
--   3. the profile is the arithmetic (equipartition) profile on the window;
--   4. the gap function is invariant under the cyclic shift of `ZMod N`.
--
--   Thus the pigeonhole inequality upgrades to a classification: the extremisers
--   are exactly the cyclically symmetric peelings.
--
--   ```lean
--   theorem Catalog.Geometry.Peel.peel_extremal_tfae(hN : 0 < N) :
--       List.TFAE
--         [ ∀ k < N, peelGap P k ≤ peelRate P N,
--           ∀ k < N, peelGap P k = peelRate P N,
--           ∀ k ≤ N, P.size k = P.size 0 - k * peelRate P N,
--           ∀ k < N, peelGap P k = peelGap P ((k + 1) % N) ] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PeelStoppingTime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PeelStoppingTime.lean#L247

-- Thm stub generated from Geometry/PeelStoppingTime.lean
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
/-
# Peeling profiles, stopping times, and the rigidity of the pigeonhole bound

A *peeling process* is the abstract skeleton shared by a large family of
geometric arguments: one removes successive "layers" from a body and records
the remaining content.  Formally the data is a nonincreasing, nonnegative
sequence `size : ℕ → ℝ` (`PeelProfile`), whose successive differences
`peelGap` are the layer contents.

The classical *upper bound* half of the theory is a pigeonhole statement:
inside any window of `N` peeling steps there is a step whose layer content is
at most the average `peelRate = (size 0 - size N)/N`.  This file formalises
that half (`exists_peel_stopping_time`, `peelEstimate_error`,
`peel_gap_density`, `exists_peel_stable_window`) and then goes further, to the
question of *sharpness*:

* `peel_extremal_tfae` — a four-way equivalence showing that the pigeonhole
  bound is saturated exactly by the arithmetic (equipartition) profiles, and
  that saturation is equivalent to invariance of the gap function under the
  cyclic shift of `ZMod N`.  This is the rigidity statement that converts the
  inequality into a classification.
* `peel_gap_const_of_pretransitive` — the group-theoretic form: if *any* group
  acts pretransitively on the `N` peeling steps and the gap function is
  invariant, all gaps equal the average.  Symmetry forces extremality.

`Catalog/Geometry/PeelSymmetryConstruction.lean` supplies the matching
geometric family of actions (equal-volume shell peelings of Euclidean balls,
equivariant for the orthogonal group).

## Lab notes

Numerical sanity checks performed while developing the file (see
`ComputationalEvidence.md`): the extremal profile for `N = 4`, `A = 1` is
`1, 3/4, 1/2, 1/4, 0`, all gaps `1/4`; the "front-loaded" profile
`1, 0, 0, 0, 0` has gaps `1, 0, 0, 0`, minimum gap `0 < 1/4`, illustrating
that the pigeonhole bound is far from an equality in general and that the
rigidity statement really needs the *uniform* smallness hypothesis.
-/

open Catalog.Geometry.Peel

open Finset

/-! ## Peeling profiles -/


variable (P : PeelProfile) {N J M k : ℕ}









/-! ## The upper bound: existence of a good stopping time -/










/-! ## Density of good stopping times -/



/-! ## Stable windows: blocks of consecutive small layers -/



/-! ## Rigidity: the pigeonhole bound is saturated only by arithmetic profiles -/

theorem Catalog.Geometry.Peel.peel_extremal_tfae(hN : 0 < N) :
    List.TFAE
      [ ∀ k < N, peelGap P k ≤ peelRate P N,
        ∀ k < N, peelGap P k = peelRate P N,
        ∀ k ≤ N, P.size k = P.size 0 - k * peelRate P N,
        ∀ k < N, peelGap P k = peelGap P ((k + 1) % N) ] := by sorry
