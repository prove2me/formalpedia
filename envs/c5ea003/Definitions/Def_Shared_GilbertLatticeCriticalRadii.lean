-- Prove2me | Definitions.Def_Shared_GilbertLatticeCriticalRadii
-- name    : Shared_GilbertLatticeCriticalRadii
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:02:04.590714+00:00
-- url     : https://prove2.me/theorems/bb6e355d-3ec0-4e45-80aa-c815e959d82f
-- title:
--   Aether Catalog definitions — Shared_GilbertLatticeCriticalRadii
-- statement:
--   Definition bundle for the Aether Catalog module Shared.GilbertLatticeCriticalRadii, transplanted by skeleton subtraction; supplies the types and constants the catalog theorems import.

-- Def bundle generated from Shared/GilbertLatticeCriticalRadii.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeConstructions
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

namespace GilbertLattice

open Set

/-- The set of radii for which some placement of the points percolates. -/
def percolatingRadii : Set ℝ :=
  {R : ℝ | ∃ (C : Config) (c : ℤ × ℤ), {d : ℤ × ℤ | (gilbert R C).Reachable c d}.Infinite}

/-- The set of radii for which *some* placement of the points gives a connected graph
(all points connected to each other). -/
def connectedPlacementRadii : Set ℝ := {R : ℝ | ∃ C : Config, (gilbert R C).Connected}

/-- The set of radii for which every placement of the points gives a connected graph. -/
def fullyConnectedRadii : Set ℝ := {R : ℝ | ∀ C : Config, (gilbert R C).Connected}

/-- The critical radius for the existence of a percolating placement. -/
noncomputable def Rmin : ℝ := sInf percolatingRadii

/-- The critical radius above which some placement connects all the points. -/
noncomputable def Rconn : ℝ := sInf connectedPlacementRadii

/-- The critical radius above which all points are connected, whatever the placement. -/
noncomputable def Rfull : ℝ := sInf fullyConnectedRadii











/-! ## The intermediate radius: some placement connects everything -/






end GilbertLattice


