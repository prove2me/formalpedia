-- Prove2me | Theorems.Thm_PythHydra_bergDepth_parent
-- name    : PythHydra.bergDepth_parent
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:11:57.740203+00:00
-- url     : https://prove2.me/theorems/dc378d68-b457-44cf-b85e-fcdfcdb93243
-- title:
--   The inverse Berggren move drops the Berggren depth by exactly one.
-- statement:
--   The inverse Berggren move drops the Berggren depth by exactly one.
--
--   ```lean
--   theorem PythHydra.bergDepth_parent{a b c : ℤ} (h : IsPPT a b c) (hc : 5 < c) :
--       bergDepth (parent a b c) + 1 = bergDepth (a, b, c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PythagoreanHydra/HydraDepth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PythagoreanHydra/HydraDepth.lean#L39

-- Thm stub generated from Geometry/PythagoreanHydra/HydraDepth.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent
import Definitions.Def_Geometry_PythagoreanHydra_HydraDepth
import Definitions.Def_Geometry_PythagoreanHydra_PythagoreanHydra

/-!
# Depth in the Berggren tree, and the sharp form of the Pythagorean Hydra bound

`PythagoreanHydra.lean` measures a head by its hypotenuse.  The *intrinsic* measure is the
depth of the head in the Berggren tree, i.e. the length of its unique address
(`BerggrenAddress.lean`).  Here we

* define `bergDepth` and prove `bergDepth (addr w) = w.length`;
* prove that the inverse Berggren move drops the depth by exactly one
  (`bergDepth_parent`), hence Berggren ancestors have strictly smaller depth;
* re-run the hydra bound with `bergDepth` as the level, obtaining the sharp statement
  `battle_depth_bound : N ≤ Phi k (H.map bergDepth)`;
* deduce that a battle starting at a node of depth `d` with branching bound `k` lasts at
  most `(k+1)^(d+1)` moves, and that a battle starting at the root `(3,4,5)` lasts at
  most **one** move.

This is the exact calibration of the Pythagorean Hydra: its length function is
`(k+1)^(depth+1)`, an elementary function of the address length — nothing like the
`ε₀`-recursive length function of the Kirby–Paris hydra.
-/

open PythHydra

theorem PythHydra.bergDepth_parent{a b c : ℤ} (h : IsPPT a b c) (hc : 5 < c) :
    bergDepth (parent a b c) + 1 = bergDepth (a, b, c) := by sorry
