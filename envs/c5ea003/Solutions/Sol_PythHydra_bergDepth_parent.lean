-- Prove2me | solution 1 for PythHydra.bergDepth_parent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:31:13.768452+00:00
-- url     : https://prove2.me/submissions/8923724b-9406-40ab-9ee9-ab6ccd91f107

-- Sol generated from Geometry/PythagoreanHydra/HydraDepth.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent
import Definitions.Def_Geometry_PythagoreanHydra_HydraDepth
import Definitions.Def_Geometry_PythagoreanHydra_PythagoreanHydra
import Theorems.Thm_PythHydra_bergDepth_addr
import Theorems.Thm_PythHydra_exists_addr
import Theorems.Thm_PythHydra_parent_addr_cons

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
theorem solution{a b c : ℤ} (h : IsPPT a b c) (hc : 5 < c) :
    bergDepth (parent a b c) + 1 = bergDepth (a, b, c) := by
  obtain ⟨w, hw⟩ := exists_addr h
  cases w with
  | nil =>
    exfalso
    simp only [addr] at hw
    have : (5 : ℤ) = c := congrArg (fun t => t.2.2) hw
    omega
  | cons s w' =>
    have hpar : parent (addr (s :: w')).1 (addr (s :: w')).2.1 (addr (s :: w')).2.2 = addr w' :=
      parent_addr_cons s w'
    rw [hw] at hpar
    simp only at hpar
    rw [hpar, ← hw, bergDepth_addr, bergDepth_addr]
    simp
