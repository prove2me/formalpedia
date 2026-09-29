-- Prove2me | Theorems.Thm_GilbertLattice_Rconn_bounds
-- name    : GilbertLattice.Rconn_bounds
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:36:42.443243+00:00
-- url     : https://prove2.me/theorems/b6a276fa-1eff-4d9c-b32f-5f872e356109
-- title:
--   Two-sided bound for the radius of a fully connected placement.
-- statement:
--   **Two-sided bound for the radius of a fully connected placement.**  The centred
--   configuration connects all the points as soon as `R > 1`, and below `1/3` no placement
--   even percolates.
--
--   ```lean
--   theorem GilbertLattice.Rconn_bounds: 1 / 3 ≤ Rconn ∧ Rconn ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeCriticalRadii.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeCriticalRadii.lean#L138

-- Thm stub generated from Shared/GilbertLatticeCriticalRadii.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeConstructions
import Definitions.Def_Shared_GilbertLatticeCriticalRadii
import Definitions.Def_Shared_GilbertLatticeLowerBound

/-!
# The two deterministic critical radii of the conditioned Gilbert model

The paper *Gilbert's disc model conditioned on the square lattice* studies, besides the
almost sure percolation threshold, two critical radii which are purely geometric:

* `GilbertLattice.Rmin`, the infimum of the radii `R` for which **some** placement of one
  point per cell of `ℤ²` produces an infinite connected component;
* `GilbertLattice.Rfull`, the infimum of the radii `R` for which **every** placement
  produces a connected graph (all points connected to each other).

This file assembles the results of the other files into two-sided bounds:

* `1/3 ≤ Rmin ≤ 1/2` (`GilbertLattice.Rmin_bounds`);
* `√17 / 2 ≤ Rfull ≤ √5` (`GilbertLattice.Rfull_bounds`).

The upper bound for `Rmin` comes from the *line configuration* (points of the rows `0`
and `1` placed alternately on the line `y = 1` at horizontal distance `1/2`), the lower
bound from the deterministic non-percolation result of `GilbertLatticeLowerBound.lean`.
The bounds for `Rfull` come from the *cut configuration* and from the fact that two
points of edge-adjacent cells are always at distance at most `√5`.
-/

open GilbertLattice

open Set

















/-! ## The intermediate radius: some placement connects everything -/

theorem GilbertLattice.Rconn_bounds: 1 / 3 ≤ Rconn ∧ Rconn ≤ 1 := by sorry
