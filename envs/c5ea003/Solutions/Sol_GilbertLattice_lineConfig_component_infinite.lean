-- Prove2me | solution 1 for GilbertLattice.lineConfig_component_infinite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:36:26.689823+00:00
-- url     : https://prove2.me/submissions/a85bc713-ed94-4412-9e64-93ca85dc3b09

-- Sol generated from Shared/GilbertLatticeConstructions.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeConstructions
import Theorems.Thm_GilbertLattice_adj_of_sqdist_lt

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



lemma px_line_zero (i : ℤ) : px lineConfig (i, 0) = (i : ℝ) + 3 / 4 := by
  simp [px, lineConfig, lineOff]

lemma px_line_one (i : ℤ) : px lineConfig (i, 1) = (i : ℝ) + 1 / 4 := by
  simp [px, lineConfig, lineOff]

lemma py_line_zero (i : ℤ) : py lineConfig (i, 0) = 1 := by
  simp [py, lineConfig, lineOff]

lemma py_line_one (i : ℤ) : py lineConfig (i, 1) = 1 := by
  simp [py, lineConfig, lineOff]

/-- In the line configuration the points of `(i,1)` and `(i,0)` are at distance `1/2`. -/
lemma adj_line_same {R : ℝ} (hR : 1 / 2 < R) (i : ℤ) :
    (gilbert R lineConfig).Adj (i, 1) (i, 0) := by
  have hR0 : (0 : ℝ) < R := by linarith
  refine adj_of_sqdist_lt hR0 (by simp) ?_
  unfold sqdist
  rw [px_line_one, px_line_zero, py_line_one, py_line_zero]
  nlinarith

/-- In the line configuration the points of `(i,0)` and `(i+1,1)` are at distance `1/2`. -/
lemma adj_line_next {R : ℝ} (hR : 1 / 2 < R) (i : ℤ) :
    (gilbert R lineConfig).Adj (i, 0) (i + 1, 1) := by
  have hR0 : (0 : ℝ) < R := by linarith
  refine adj_of_sqdist_lt hR0 (by simp) ?_
  unfold sqdist
  rw [px_line_zero, px_line_one, py_line_zero, py_line_one]
  push_cast
  nlinarith

/-- Consecutive cells of the bottom row are connected in the line configuration. -/
lemma reachable_line_succ {R : ℝ} (hR : 1 / 2 < R) (i : ℤ) :
    (gilbert R lineConfig).Reachable (i, 0) (i + 1, 0) :=
  ((adj_line_next hR i).reachable).trans ((adj_line_same hR (i + 1)).reachable)

/-- All cells `(n, 0)`, `n : ℕ`, lie in the connected component of `(0,0)`. -/
lemma reachable_line_nat {R : ℝ} (hR : 1 / 2 < R) (n : ℕ) :
    (gilbert R lineConfig).Reachable (0, 0) ((n : ℤ), 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine ih.trans ?_
      have := reachable_line_succ hR (n : ℤ)
      simpa [Nat.cast_succ] using this



/-! ## The centred configuration -/



/-! ## The cut configuration -/









open GilbertLattice in
theorem solution{R : ℝ} (hR : 1 / 2 < R) :
    {c : ℤ × ℤ | (gilbert R lineConfig).Reachable (0, 0) c}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (((n : ℤ)), (0 : ℤ)))
  · intro a b hab
    simpa using hab
  · intro n
    exact reachable_line_nat hR n
