-- Prove2me | Definitions.Def_Shared_GilbertLatticeDiagonalCut
-- name    : Shared_GilbertLatticeDiagonalCut
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:02:55.755255+00:00
-- url     : https://prove2.me/theorems/ed956973-3d2a-4aea-95f1-4e5993c0ef0c
-- title:
--   Aether Catalog definitions — Shared_GilbertLatticeDiagonalCut
-- statement:
--   Definition bundle for the Aether Catalog module Shared.GilbertLatticeDiagonalCut, transplanted by skeleton subtraction; supplies the types and constants the catalog theorems import.

-- Def bundle generated from Shared/GilbertLatticeDiagonalCut.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeCriticalRadii

/-!
# The exact value of the full-connectivity radius: `R_full = √5`

For the model *Gilbert's disc model conditioned on the square lattice* (one point per
cell of `ℤ²`, two points joined when their distance is `< R`) the file
`GilbertLatticeCriticalRadii.lean` bounds the radius of *full connectivity*

`R_full = inf {R : for every placement of the points, the graph is connected}`

between `√17 / 2 ≈ 2.0616` (a horizontal cut) and `√5 ≈ 2.2360`.

This file closes the gap: it produces a placement built along a **diagonal** cut for
which every crossing pair of points is at distance at least `√5`, so that the graph is
disconnected for every `R ≤ √5`.  Together with the upper bound of
`GilbertLatticeConnectivity.lean` this gives the exact value

* `GilbertLattice.Rfull_eq_sqrt_five` : `R_full = √5`,

and even the exact description of the set of radii of full connectivity,

* `GilbertLattice.fullyConnectedRadii_eq` : `{R : every placement is connected} = (√5, ∞)`.

## The diagonal configuration

Cells are split along the diagonal: `c` is *upper* when `c.1 ≤ c.2` and *lower*
otherwise.  The point of an upper cell is pushed to the top-left corner of the cell,
the point of a lower cell to the bottom-right corner.  If `c` is upper and `c'` is
lower, the displacement between the two points is `(u, v)` with

`u = c.1 - c'.1 - 1`,  `v = c.2 + 1 - c'.2`,  and  `v ≥ u + 3`;

over the integers this forces `u² + v² ≥ 5` (`GilbertLattice.five_le_sq_add_sq`), the
minimum `5` being attained at `(u, v) = (-1, 2)` and `(-2, 1)`.  Note that the naive
continuous bound would only give `u² + v² ≥ 9/2`: the value `5` is genuinely arithmetic.
-/

namespace GilbertLattice


/-- Offsets of the diagonal cut configuration: cells above the diagonal put their point
at the top-left corner, cells below it at the bottom-right corner. -/
noncomputable def diagOff : ℤ × ℤ → ℝ × ℝ := fun c => if c.1 ≤ c.2 then (0, 1) else (1, 0)

/-- The diagonal cut configuration. -/
noncomputable def diagConfig : Config where
  off := diagOff
  off_nonneg_fst := by intro c; unfold diagOff; split_ifs <;> norm_num
  off_nonneg_snd := by intro c; unfold diagOff; split_ifs <;> norm_num
  off_le_one_fst := by intro c; unfold diagOff; split_ifs <;> norm_num
  off_le_one_snd := by intro c; unfold diagOff; split_ifs <;> norm_num














end GilbertLattice


