-- Prove2me | Theorems.Thm_GilbertLattice_sqrt_five_lt_of_mem_fullyConnectedRadii
-- name    : GilbertLattice.sqrt_five_lt_of_mem_fullyConnectedRadii
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:37:30.967898+00:00
-- url     : https://prove2.me/theorems/5a8eba51-ed19-44da-950a-7d4a51eaf2c0
-- title:
--   Any radius of full connectivity is `> â5`.
-- statement:
--   Any radius of full connectivity is `> â5`.
--
--   ```lean
--   theorem GilbertLattice.sqrt_five_lt_of_mem_fullyConnectedRadii{R : ℝ} (hR : R ∈ fullyConnectedRadii) :
--       Real.sqrt 5 < R := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeDiagonalCut.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeDiagonalCut.lean#L126

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

theorem GilbertLattice.sqrt_five_lt_of_mem_fullyConnectedRadii{R : ℝ} (hR : R ∈ fullyConnectedRadii) :
    Real.sqrt 5 < R := by sorry
