-- Prove2me | Theorems.Thm_ToricCode_hWind_of_boundary
-- name    : ToricCode.hWind_of_boundary
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:13:12.735761+00:00
-- url     : https://prove2.me/theorems/afacf473-94c4-4cc7-8243-83397563b4c9
-- title:
--   HWind of boundary
-- statement:
--   Formal statement of `ToricCode.hWind_of_boundary` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ToricCode.hWind_of_boundary(g : Face M N → F2) (i : ZMod M) :
--       hWind M N (d2 M N *ᵥ g) i = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Distance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Distance.lean#L117

-- Thm stub generated from Geometry/ToricCode/Distance.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Homology
/-!
# The `Z`-distance of the `M × N` toric code is exactly `min M N`

This is the geometric heart of the development.  For the grid cellulation of the
torus `(ℤ/M) × (ℤ/N)` we prove

  `distance M N = min M N`,

i.e. the minimal Hamming weight of a cellular one-cycle that is not a boundary
is exactly the smaller of the two side lengths.  Together with
`ToricCode.toric_homologyRank` this establishes the parameters
`[[2MN, 2, min M N]]`, specialising to the classical `[[2L², 2, L]]` for the
square torus.

## Strategy

For each `i : ZMod M` the *column cut* consists of the `N` horizontal edges
`(false, (i, y))`.  The parity of a chain on this cut is `hWind z i`.  Dually
`vWind z j` is the parity on the *row cut* of vertical edges `(true, (x, j))`.

* `hWind_const` / `vWind_const`: for a cycle these parities do not depend on the
  cut.  (This is discrete Stokes: the difference of two neighbouring cut parities
  is the sum of the vertex boundary over a column.)
* `hWind_of_boundary` / `vWind_of_boundary`: they vanish on boundaries.
* `winding_ne_zero_of_not_boundary`: conversely, a cycle with both windings zero
  *is* a boundary.  This is proved by a dimension count: the winding map
  `cycles → 𝔽₂²` is onto, so its kernel has dimension `MN - 1`, which is exactly
  the dimension of the boundary space computed in `ToricCode.Homology`.
* Hence a logical operator has odd parity on each of the `M` pairwise disjoint
  column cuts, or on each of the `N` pairwise disjoint row cuts, so it uses at
  least `min M N` edges; and the two coordinate loops, of weights `M` and `N`,
  realise the bound.
-/

open Matrix

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]

/-! ### Winding parities -/









/-! ### Windings vanish on boundaries -/

theorem ToricCode.hWind_of_boundary(g : Face M N → F2) (i : ZMod M) :
    hWind M N (d2 M N *ᵥ g) i = 0 := by sorry
