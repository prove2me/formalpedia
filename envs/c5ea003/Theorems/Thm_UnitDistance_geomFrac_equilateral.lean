-- Prove2me | Theorems.Thm_UnitDistance_geomFrac_equilateral
-- name    : UnitDistance.geomFrac_equilateral
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:03:16.331637+00:00
-- url     : https://prove2.me/theorems/fbda7e84-8381-45ac-b524-a7f31d819621
-- title:
--   Concrete geometric value.
-- statement:
--   **Concrete geometric value.**  The unit equilateral triangle has geometric
--   fractional chromatic number exactly `3`.  This is the tight small-scale analogue of
--   the `MRVZ` graph `G_27`, whose value is exactly `4`.
--
--   ```lean
--   theorem UnitDistance.geomFrac_equilateral: geomFrac (unitDistanceGraph equilateral) = 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RamseyTheory/UnitDistanceFractional.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RamseyTheory/UnitDistanceFractional.lean#L120

-- Thm stub generated from Geometry/UnitDistanceFractional.lean
import Mathlib
import Definitions.Def_Geometry_GeomFractionalChromatic
import Definitions.Def_Geometry_UnitDistanceFractional
/-
Copyright (c) 2026. All rights reserved.

# Unit-distance graphs and the fractional-chromatic engine

This file supplies the *geometric payload* for the independence-ratio engine of
`GeomFractionalChromatic.lean`, in the spirit of Matolcsi–Ruzsa–Varga–Zsámboki
(`MRVZ`), de Grey (`deGrey`) and Erdős (`Er87`).

We define the **unit-distance graph** on a finite family of points of the
Euclidean plane, characterise its independent sets geometrically, and connect it
to the LP lower bound `geomFrac G ≥ |V| / α(G)`.

## Main results

* `unitDistanceGraph` — the unit-distance graph of `p : V → ℝ²`.
* `unitDistanceGraph_adj_iff` / `isIndepSet_iff_no_unit` — the geometric reading:
  an independent set is a set of points with **no two at distance exactly `1`**.
* `equilateral` — a concrete equilateral triangle whose three vertices are
  pairwise at distance `1`; its unit-distance graph is complete, so its geometric
  fractional chromatic number is exactly `3` (`geomFrac_equilateral`).  This is the
  small-scale analogue of the `MRVZ` graph `G_27`, whose value is exactly `4`.
* `geomFrac_top_fin5_gt_four` — a concrete graph reaching the strict regime
  `geomFrac > 4`, showing the engine's conclusion is attainable.
* `exists_geomFrac_gt_four_of_low_indep_ratio` — **the MRVZ reduction as a bridge
  theorem**: the existence of *any* finite graph with independence ratio `< 1/4`
  yields a graph with geometric fractional chromatic number `> 4`.  Combined with a
  unit-distance realisation, this is precisely the statement that the fractional
  chromatic number of the plane exceeds `4`.
-/

open SimpleGraph Finset GeomFrac
open scoped BigOperators

open UnitDistance





/-! ### A concrete equilateral triangle -/

theorem UnitDistance.geomFrac_equilateral: geomFrac (unitDistanceGraph equilateral) = 3 := by sorry
