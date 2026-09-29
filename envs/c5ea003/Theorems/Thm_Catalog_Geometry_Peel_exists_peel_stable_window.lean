-- Prove2me | Theorems.Thm_Catalog_Geometry_Peel_exists_peel_stable_window
-- name    : Catalog.Geometry.Peel.exists_peel_stable_window
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:06:40.474736+00:00
-- url     : https://prove2.me/theorems/ce78c9bd-cf76-4f1a-8bbd-514168cddea8
-- title:
--   Stable window.
-- statement:
--   **Stable window.**  Splitting `N = J * M` steps into `M` blocks of length
--   `J`, some block removes at most `J / N` of the budget, and hence *every* layer
--   inside that block is that small.
--
--   ```lean
--   theorem Catalog.Geometry.Peel.exists_peel_stable_window(hM : 0 < M) :
--       ∃ b < M, (∀ j < J, peelGap P (J * b + j) ≤ (P.size 0 - P.size (J * M)) / M) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PeelStoppingTime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PeelStoppingTime.lean#L228

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

theorem Catalog.Geometry.Peel.exists_peel_stable_window(hM : 0 < M) :
    ∃ b < M, (∀ j < J, peelGap P (J * b + j) ≤ (P.size 0 - P.size (J * M)) / M) := by sorry
