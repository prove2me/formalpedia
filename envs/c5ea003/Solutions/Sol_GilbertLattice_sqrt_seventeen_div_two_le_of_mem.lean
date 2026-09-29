-- Prove2me | solution 1 for GilbertLattice.sqrt_seventeen_div_two_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:18:39.295765+00:00
-- url     : https://prove2.me/submissions/c51db452-a96c-4373-bc1c-0c9503e64e9f

-- Sol generated from Shared/GilbertLatticeCriticalRadii.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeConstructions
import Definitions.Def_Shared_GilbertLatticeCriticalRadii
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_cutConfig_not_connected
import Theorems.Thm_GilbertLattice_radius_pos_of_adj

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
lemma solution{R : ℝ} (hR : R ∈ fullyConnectedRadii) :
    Real.sqrt 17 / 2 ≤ R := by
  by_contra hcon
  push_neg at hcon
  have h17 : (0 : ℝ) ≤ 17 := by norm_num
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt h17
  have hsnn : (0 : ℝ) ≤ Real.sqrt 17 := Real.sqrt_nonneg 17
  have hRpos : 0 < R := by
    by_contra hle
    push_neg at hle
    obtain ⟨w⟩ := (hR cutConfig).preconnected (0, 0) (1, 0)
    cases w with
    | cons hadj w' => exact absurd (radius_pos_of_adj hadj) (not_lt.2 hle)
  have hR2 : R ^ 2 ≤ 17 / 4 := by nlinarith [hcon, hsnn, hs, hRpos]
  exact cutConfig_not_connected hR2 (hR cutConfig)
