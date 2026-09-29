-- Prove2me | Theorems.Thm_GilbertLattice_five_le_sqdist_diag
-- name    : GilbertLattice.five_le_sqdist_diag
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:37:20.994971+00:00
-- url     : https://prove2.me/theorems/83ded345-ff7a-47bd-ab08-6dce461678e7
-- title:
--   The diagonal cut is `â5`-wide.
-- statement:
--   **The diagonal cut is `â5`-wide.**  In the diagonal configuration, the point of a
--   cell above the diagonal and the point of a cell below it are at squared distance at
--   least `5`.
--
--   ```lean
--   theorem GilbertLattice.five_le_sqdist_diag{c c' : ℤ × ℤ} (hc : c.1 ≤ c.2) (hc' : ¬ c'.1 ≤ c'.2) :
--       5 ≤ sqdist diagConfig c c' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeDiagonalCut.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeDiagonalCut.lean#L75

-- Thm stub generated from Shared/GilbertLatticeDiagonalCut.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeCriticalRadii
import Definitions.Def_Shared_GilbertLatticeDiagonalCut

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

open GilbertLattice

theorem GilbertLattice.five_le_sqdist_diag{c c' : ℤ × ℤ} (hc : c.1 ≤ c.2) (hc' : ¬ c'.1 ≤ c'.2) :
    5 ≤ sqdist diagConfig c c' := by sorry
