-- Prove2me | Definitions.Def_Geometry_PadicBerggrenNullCone
-- name    : Geometry_PadicBerggrenNullCone
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:15.747376+00:00
-- url     : https://prove2.me/theorems/552ffcb5-392f-4448-8b3b-ce6abd385e67
-- title:
--   Aether Catalog definitions — Geometry_PadicBerggrenNullCone
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PadicBerggrenNullCone`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PadicBerggrenNullCone.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics

/-!
# The size of the p-adic Berggren null cone

`Catalog/Geometry/PadicBerggrenDynamics.lean` sets up the three Berggren (Barning–Hall)
generators as a dynamical system on `(ZMod (p^k))³` preserving the Lorentz form
`q(a,b,c) = a² + b² − c²`.  Every state of that system lives on the **null cone**
`q = 0`, and the whole Berggren tree reduces into it.

This file computes the exact size of the phase space:

* `PadicBerggren.card_nullCone` : for every odd prime `p` the null cone mod `p` has
  **exactly `p²` points**.  The proof fibres the cone over the linear functional
  `w ↦ w 2 − w 0` (the "light-cone coordinate" `c − a`) and shows that *every* fibre —
  including the degenerate one over `0` — has exactly `p` points.  This is the counting
  incarnation of the fact that `q` is a nondegenerate isotropic ternary form.
* `PadicBerggren.card_nullCone_nonzero` : `p² − 1` nonzero null vectors, i.e. `p + 1`
  projective null points each carrying `p − 1` nonzero vectors.
* `PadicBerggren.tree_collision_nullCone` : since the whole depth-`d` tree lands inside the
  null cone, two distinct words already collide mod `p` as soon as `3^d > p²`.  This is a
  quadratic (in `p`) obstruction, far stronger than the naive cubic bound
  `tree_collision_mod`, and it says that the reduction of the boundary of the tree has
  "box dimension at most 2": the tree cannot inject into any single finite level.
-/

namespace PadicBerggren

open Matrix Finset

variable (p : ℕ) [Fact p.Prime]

/-- The null cone mod `p`, as a finset (the phase space of the reduced Berggren dynamics). -/
def nullConeFinset : Finset (Fin 3 → ZMod p) :=
  univ.filter (fun w => lorentz (ZMod p) w = 0)









end PadicBerggren


