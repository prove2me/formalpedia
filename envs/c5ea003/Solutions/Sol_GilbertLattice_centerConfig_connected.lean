-- Prove2me | solution 1 for GilbertLattice.centerConfig_connected
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:14:16.000853+00:00
-- url     : https://prove2.me/submissions/3b44fe5e-f2c1-4b7e-a514-b176510f9a34

-- Sol generated from Shared/GilbertLatticeConstructions.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeConstructions
import Theorems.Thm_GilbertLattice_adj_of_sqdist_lt
import Theorems.Thm_GilbertLattice_connected_of_grid_adj

/-!
# Two explicit configurations of the conditioned Gilbert model

This file contains the two extremal *placements* of the points which govern two of the
three critical radii of the model.

## The line configuration and the radius `1/2`

`GilbertLattice.lineConfig` puts the point of the cell `(i,0)` at `(i + 3/4, 1)` and the
point of the cell `(i,1)` at `(i + 1/4, 1)`.  All these points lie on the horizontal line
`y = 1` and consecutive ones are at distance exactly `1/2`, so as soon as `R > 1/2` the
whole double row `ℤ × {0,1}` is one infinite connected component
(`GilbertLattice.lineConfig_component_infinite`).

Thus the *geometric* critical radius
`R_min = inf {R : some placement of the points percolates}` satisfies `R_min ≤ 1/2`;
the companion file `GilbertLatticeLowerBound.lean` proves `R_min ≥ 1/3`.

## The cut configuration and full connectivity

`GilbertLattice.cutConfig` pushes the points of the rows `j ≥ 1` up to the line
`y = j+1` and staggers them horizontally by `1/2`, while the points of the rows `j ≤ 0`
are pushed down to the line `y = j`.  Two points on opposite sides of the horizontal
line `y = 1` are then at distance at least `√17 / 2 ≈ 2.0616`, so for `R ≤ √17/2` the
graph is disconnected.  Hence the critical radius for full connectivity satisfies
`R_full ≥ √17/2` (`GilbertLattice.cutConfig_not_connected`), to be compared with the
upper bound `R_full ≤ √5 ≈ 2.2360` proved in `GilbertLatticeConnectivity.lean`.
-/

open GilbertLattice

/-! ## The line configuration -/













/-! ## The centred configuration -/



/-! ## The cut configuration -/









open GilbertLattice in
theorem solution{R : ℝ} (hR : 1 < R) : (gilbert R centerConfig).Connected := by
  have hR0 : (0 : ℝ) < R := by linarith
  refine connected_of_grid_adj (fun i j => ?_) (fun i j => ?_)
  · refine adj_of_sqdist_lt hR0 (by intro h; rw [Prod.ext_iff] at h; omega) ?_
    unfold sqdist px py centerConfig
    push_cast
    nlinarith
  · refine adj_of_sqdist_lt hR0 (by intro h; rw [Prod.ext_iff] at h; omega) ?_
    unfold sqdist px py centerConfig
    push_cast
    nlinarith
