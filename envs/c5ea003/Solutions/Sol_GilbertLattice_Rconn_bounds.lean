-- Prove2me | solution 1 for GilbertLattice.Rconn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:27:23.351026+00:00
-- url     : https://prove2.me/submissions/9fd6bc30-f1fd-4ede-bc35-cc0a6b9e00a7

-- Sol generated from Shared/GilbertLatticeCriticalRadii.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeConstructions
import Definitions.Def_Shared_GilbertLatticeCriticalRadii
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_centerConfig_connected
import Theorems.Thm_GilbertLattice_not_infinite_component

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








lemma one_third_le_of_mem_percolatingRadii {R : ℝ} (hR : R ∈ percolatingRadii) :
    1 / 3 ≤ R := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨C, c, hc⟩ := hR
  exact not_infinite_component (C := C) hcon c hc









/-! ## The intermediate radius: some placement connects everything -/

lemma connectedPlacement_subset_percolating :
    connectedPlacementRadii ⊆ percolatingRadii := by
  rintro R ⟨C, hC⟩
  refine ⟨C, (0, 0), ?_⟩
  have : {d : ℤ × ℤ | (gilbert R C).Reachable (0, 0) d} = Set.univ := by
    ext d
    simp [hC.preconnected (0, 0) d]
  rw [this]
  exact Set.infinite_univ


lemma connectedPlacementRadii_nonempty : connectedPlacementRadii.Nonempty :=
  ⟨2, centerConfig, centerConfig_connected (by norm_num)⟩




open GilbertLattice in
theorem solution: 1 / 3 ≤ Rconn ∧ Rconn ≤ 1 := by
  constructor
  · refine le_csInf connectedPlacementRadii_nonempty fun R hR => ?_
    exact one_third_le_of_mem_percolatingRadii (connectedPlacement_subset_percolating hR)
  · have hsub : Ioi (1 : ℝ) ⊆ connectedPlacementRadii := fun R hR =>
      ⟨centerConfig, centerConfig_connected hR⟩
    have hbdd : BddBelow connectedPlacementRadii :=
      ⟨1 / 3, fun R hR =>
        one_third_le_of_mem_percolatingRadii (connectedPlacement_subset_percolating hR)⟩
    have h1 : sInf connectedPlacementRadii ≤ sInf (Ioi (1 : ℝ)) :=
      csInf_le_csInf hbdd ⟨2, by norm_num⟩ hsub
    rwa [csInf_Ioi] at h1
