-- Prove2me | Definitions.Def_Shared_GilbertLatticeConstructions
-- name    : Shared_GilbertLatticeConstructions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:00:11.71024+00:00
-- url     : https://prove2.me/theorems/67b6a456-37b4-4c53-ae5c-b7fd5a67aa9c
-- title:
--   Aether Catalog definitions — Shared_GilbertLatticeConstructions
-- statement:
--   Definition bundle for the Aether Catalog module Shared.GilbertLatticeConstructions, transplanted by skeleton subtraction; supplies the types and constants the catalog theorems import.

-- Def bundle generated from Shared/GilbertLatticeConstructions.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2

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

namespace GilbertLattice

/-! ## The line configuration -/

/-- Offsets of the line configuration: the points of the two rows `j = 0` and `j = 1`
are placed on the line `y = 1`, alternately at abscissa `i + 3/4` and `i + 1/4`. -/
noncomputable def lineOff : ℤ × ℤ → ℝ × ℝ := fun c =>
  if c.2 = 0 then (3 / 4, 1) else if c.2 = 1 then (1 / 4, 0) else (0, 0)

/-- The line configuration. -/
noncomputable def lineConfig : Config where
  off := lineOff
  off_nonneg_fst := by intro c; unfold lineOff; split_ifs <;> norm_num
  off_nonneg_snd := by intro c; unfold lineOff; split_ifs <;> norm_num
  off_le_one_fst := by intro c; unfold lineOff; split_ifs <;> norm_num
  off_le_one_snd := by intro c; unfold lineOff; split_ifs <;> norm_num











/-! ## The centred configuration -/

/-- The configuration placing every point at the centre of its cell. -/
noncomputable def centerConfig : Config where
  off := fun _ => (1 / 2, 1 / 2)
  off_nonneg_fst := by intro c; norm_num
  off_nonneg_snd := by intro c; norm_num
  off_le_one_fst := by intro c; norm_num
  off_le_one_snd := by intro c; norm_num


/-! ## The cut configuration -/

/-- Offsets of the cut configuration: the rows `j ≥ 1` are pushed up to the top of their
cell and shifted right by `1/2`, the rows `j ≤ 0` are pushed to the bottom-left corner. -/
noncomputable def cutOff : ℤ × ℤ → ℝ × ℝ := fun c => if 1 ≤ c.2 then (1 / 2, 1) else (0, 0)

/-- The cut configuration. -/
noncomputable def cutConfig : Config where
  off := cutOff
  off_nonneg_fst := by intro c; unfold cutOff; split_ifs <;> norm_num
  off_nonneg_snd := by intro c; unfold cutOff; split_ifs <;> norm_num
  off_le_one_fst := by intro c; unfold cutOff; split_ifs <;> norm_num
  off_le_one_snd := by intro c; unfold cutOff; split_ifs <;> norm_num






end GilbertLattice


