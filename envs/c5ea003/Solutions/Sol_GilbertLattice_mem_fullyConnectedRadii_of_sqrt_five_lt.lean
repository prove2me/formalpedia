-- Prove2me | solution 1 for GilbertLattice.mem_fullyConnectedRadii_of_sqrt_five_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:18:38.802684+00:00
-- url     : https://prove2.me/submissions/33b4518d-76ed-4d63-ae7c-230448000217

-- Sol generated from Shared/GilbertLatticeCriticalRadii.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeConstructions
import Definitions.Def_Shared_GilbertLatticeCriticalRadii
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_connected_of_sqrt_five_lt

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







open GilbertLattice in
lemma solution{R : ℝ} (hR : Real.sqrt 5 < R) :
    R ∈ fullyConnectedRadii := fun C => connected_of_sqrt_five_lt C hR
