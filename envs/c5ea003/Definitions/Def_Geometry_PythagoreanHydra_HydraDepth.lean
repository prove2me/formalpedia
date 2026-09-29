-- Prove2me | Definitions.Def_Geometry_PythagoreanHydra_HydraDepth
-- name    : Geometry_PythagoreanHydra_HydraDepth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T13:07:51.167736+00:00
-- url     : https://prove2.me/theorems/62158c42-82c9-4567-9432-e03486a39852
-- title:
--   Aether Catalog definitions — Geometry_PythagoreanHydra_HydraDepth
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PythagoreanHydra.HydraDepth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PythagoreanHydra/HydraDepth.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
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

namespace PythHydra

open Classical in
/-- The depth of a triple in the Berggren tree: the length of its (unique) address. -/
noncomputable def bergDepth (t : ℤ × ℤ × ℤ) : ℕ :=
  if h : ∃ w : List BStep, addr w = t then h.choose.length else 0












end PythHydra


