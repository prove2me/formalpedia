-- Prove2me | solution 1 for GilbertLattice.cutConfig_no_crossing_edge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:33:23.667395+00:00
-- url     : https://prove2.me/submissions/9dd1cacb-a223-4295-83b0-b51ee5fb73dd

-- Sol generated from Shared/GilbertLatticeConstructions.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeConstructions
import Theorems.Thm_GilbertLattice_not_adj_of_le_sqdist

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
lemma solution{R : ℝ} (hR : R ^ 2 ≤ 17 / 4) {c c' : ℤ × ℤ}
    (hc : 1 ≤ c.2) (hc' : c'.2 ≤ 0) : ¬ (gilbert R cutConfig).Adj c c' := by
  refine not_adj_of_le_sqdist (le_trans hR ?_)
  have hpx : px cutConfig c = (c.1 : ℝ) + 1 / 2 := by
    simp [px, cutConfig, cutOff, hc]
  have hpy : py cutConfig c = (c.2 : ℝ) + 1 := by
    simp [py, cutConfig, cutOff, hc]
  have hpx' : px cutConfig c' = (c'.1 : ℝ) := by
    have : ¬ (1 ≤ c'.2) := by omega
    simp [px, cutConfig, cutOff, this]
  have hpy' : py cutConfig c' = (c'.2 : ℝ) := by
    have : ¬ (1 ≤ c'.2) := by omega
    simp [py, cutConfig, cutOff, this]
  unfold sqdist
  rw [hpx, hpy, hpx', hpy']
  have hy : (2 : ℝ) ≤ ((c.2 : ℝ) + 1) - (c'.2 : ℝ) := by
    have h : (c'.2 : ℤ) + 1 ≤ c.2 := by omega
    have h' : ((c'.2 : ℤ) : ℝ) + 1 ≤ ((c.2 : ℤ) : ℝ) := by exact_mod_cast h
    linarith
  have hx : (1 / 2 : ℝ) ≤ |((c.1 : ℝ) + 1 / 2) - (c'.1 : ℝ)| := by
    by_cases h : (c'.1 : ℤ) ≤ c.1
    · have h' : ((c'.1 : ℤ) : ℝ) ≤ ((c.1 : ℤ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have h2 : (c.1 : ℤ) + 1 ≤ c'.1 := by omega
      have h' : ((c.1 : ℤ) : ℝ) + 1 ≤ ((c'.1 : ℤ) : ℝ) := by exact_mod_cast h2
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hx2 : (1 / 4 : ℝ) ≤ (((c.1 : ℝ) + 1 / 2) - (c'.1 : ℝ)) ^ 2 := by
    have := sq_abs (((c.1 : ℝ) + 1 / 2) - (c'.1 : ℝ))
    nlinarith [abs_nonneg (((c.1 : ℝ) + 1 / 2) - (c'.1 : ℝ))]
  nlinarith
