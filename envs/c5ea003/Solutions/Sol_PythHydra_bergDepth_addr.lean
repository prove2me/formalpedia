-- Prove2me | solution 1 for PythHydra.bergDepth_addr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:28:10.557904+00:00
-- url     : https://prove2.me/submissions/cc977ebc-371c-4240-87f0-3acd9a7b1f68

-- Sol generated from Geometry/PythagoreanHydra/HydraDepth.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_HydraDepth
import Definitions.Def_Geometry_PythagoreanHydra_PythagoreanHydra
import Theorems.Thm_PythHydra_addr_injective

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














open PythHydra in
theorem solution(w : List BStep) : bergDepth (addr w) = w.length := by
  have h : ∃ w' : List BStep, addr w' = addr w := ⟨w, rfl⟩
  rw [bergDepth, dif_pos h]
  exact congrArg List.length (addr_injective h.choose_spec)
