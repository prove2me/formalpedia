-- Prove2me | solution 1 for GilbertLattice.cutConfig_not_connected
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:35:06.142027+00:00
-- url     : https://prove2.me/submissions/5bcc7eb8-c284-4c54-b52b-e3c1e58b32fd

-- Sol generated from Shared/GilbertLatticeConstructions.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeConstructions
import Theorems.Thm_GilbertLattice_cutConfig_no_crossing_edge

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




/-- The upper half plane is stable under the adjacency relation of the cut
configuration. -/
lemma cutConfig_upper_closed {R : ℝ} (hR : R ^ 2 ≤ 17 / 4) {c c' : ℤ × ℤ}
    (hadj : (gilbert R cutConfig).Adj c c') (hc : 1 ≤ c.2) : 1 ≤ c'.2 := by
  by_contra hcon
  exact cutConfig_no_crossing_edge hR hc (by omega) hadj

/-- The upper half plane is stable under reachability in the cut configuration. -/
lemma cutConfig_reachable_upper {R : ℝ} (hR : R ^ 2 ≤ 17 / 4) {c c' : ℤ × ℤ}
    (h : (gilbert R cutConfig).Reachable c c') (hc : 1 ≤ c.2) : 1 ≤ c'.2 := by
  obtain ⟨w⟩ := h
  revert hc
  induction w with
  | nil => exact id
  | cons hadj w ih => exact fun hc => ih (cutConfig_upper_closed hR hadj hc)

/-- **Lower bound for the radius of full connectivity.**  For `R ≤ √17/2` there is a
placement of the points whose Gilbert graph is disconnected: the cells `(0,1)` and
`(0,0)` are in different components. -/
theorem cutConfig_not_reachable {R : ℝ} (hR : R ^ 2 ≤ 17 / 4) :
    ¬ (gilbert R cutConfig).Reachable (0, 1) (0, 0) := by
  intro h
  have := cutConfig_reachable_upper hR h (by norm_num)
  norm_num at this



open GilbertLattice in
theorem solution{R : ℝ} (hR : R ^ 2 ≤ 17 / 4) :
    ¬ (gilbert R cutConfig).Connected := fun h =>
  cutConfig_not_reachable hR (h.preconnected (0, 1) (0, 0))
