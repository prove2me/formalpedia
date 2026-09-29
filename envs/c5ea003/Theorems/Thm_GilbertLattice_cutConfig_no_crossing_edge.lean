-- Prove2me | Theorems.Thm_GilbertLattice_cutConfig_no_crossing_edge
-- name    : GilbertLattice.cutConfig_no_crossing_edge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:24:53.433993+00:00
-- url     : https://prove2.me/theorems/f39c2e30-9417-422e-a2c0-2755da68c842
-- title:
--   Cut config no crossing edge
-- statement:
--   Formal statement of `GilbertLattice.cutConfig_no_crossing_edge` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GilbertLattice.cutConfig_no_crossing_edge{R : ℝ} (hR : R ^ 2 ≤ 17 / 4) {c c' : ℤ × ℤ}
--       (hc : 1 ≤ c.2) (hc' : c'.2 ≤ 0) : ¬ (gilbert R cutConfig).Adj c c' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeConstructions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeConstructions.lean#L151

-- Thm stub generated from Shared/GilbertLatticeConstructions.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeConstructions

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

theorem GilbertLattice.cutConfig_no_crossing_edge{R : ℝ} (hR : R ^ 2 ≤ 17 / 4) {c c' : ℤ × ℤ}
    (hc : 1 ≤ c.2) (hc' : c'.2 ≤ 0) : ¬ (gilbert R cutConfig).Adj c c' := by sorry
