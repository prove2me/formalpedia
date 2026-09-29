-- Prove2me | Theorems.Thm_GilbertLattice_mem_fullyConnectedRadii_of_sqrt_five_lt
-- name    : GilbertLattice.mem_fullyConnectedRadii_of_sqrt_five_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:27:18.222649+00:00
-- url     : https://prove2.me/theorems/1f9ee771-e872-41de-aed2-40142f1de8e0
-- title:
--   Mem fully connected radii of sqrt five lt
-- statement:
--   Formal statement of `GilbertLattice.mem_fullyConnectedRadii_of_sqrt_five_lt` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GilbertLattice.mem_fullyConnectedRadii_of_sqrt_five_lt{R : ℝ} (hR : Real.sqrt 5 < R) :
--       R ∈ fullyConnectedRadii := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeCriticalRadii.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeCriticalRadii.lean#L79

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

theorem GilbertLattice.mem_fullyConnectedRadii_of_sqrt_five_lt{R : ℝ} (hR : Real.sqrt 5 < R) :
    R ∈ fullyConnectedRadii := by sorry
