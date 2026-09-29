-- Prove2me | Theorems.Thm_PythHydra_battle_depth_bound
-- name    : PythHydra.battle_depth_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:11:50.409914+00:00
-- url     : https://prove2.me/theorems/9f131939-50a3-4237-8ca0-d0f8b59c38f3
-- title:
--   Sharp length bound for the Pythagorean Hydra, in terms of Berggren depth.
-- statement:
--   **Sharp length bound for the Pythagorean Hydra**, in terms of Berggren depth.
--
--   ```lean
--   theorem PythHydra.battle_depth_bound{k N : ℕ} {H H' : Multiset (ℤ × ℤ × ℤ)} (h : Battle k N H H') :
--       N ≤ Phi k (H.map bergDepth) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PythagoreanHydra/HydraDepth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PythagoreanHydra/HydraDepth.lean#L91

-- Thm stub generated from Geometry/PythagoreanHydra/HydraDepth.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_HydraDepth
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
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

theorem PythHydra.battle_depth_bound{k N : ℕ} {H H' : Multiset (ℤ × ℤ × ℤ)} (h : Battle k N H H') :
    N ≤ Phi k (H.map bergDepth) := by sorry
