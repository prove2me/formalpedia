-- Prove2me | Theorems.Thm_PadicBerggren_card_nullCone_fiber
-- name    : PadicBerggren.card_nullCone_fiber
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:34:48.311795+00:00
-- url     : https://prove2.me/theorems/a231fe9e-bb3e-45d0-ab50-f65d0415397e
-- title:
--   Every light-cone fibre has exactly `p` points.
-- statement:
--   **Every light-cone fibre has exactly `p` points.**  Fibring the null cone over the
--   linear functional `w ↦ w 2 − w 0`, the fibre over a unit `u` is the graph
--   `b ↦ ((b²/u − u)/2, b, (b²/u + u)/2)` and the fibre over `0` is the isotropic line
--   `s ↦ (s, 0, s)`; both are parametrised bijectively by `ZMod p`.
--
--   ```lean
--   theorem PadicBerggren.card_nullCone_fiber(hp : p ≠ 2) (u : ZMod p) :
--       ((nullConeFinset p).filter (fun w => w 2 - w 0 = u)).card = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PadicBerggrenNullCone.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PadicBerggrenNullCone.lean#L52

-- Thm stub generated from Geometry/PadicBerggrenNullCone.lean
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics
import Definitions.Def_Geometry_PadicBerggrenNullCone

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

open PadicBerggren

open Matrix Finset

variable (p : ℕ) [Fact p.Prime]

theorem PadicBerggren.card_nullCone_fiber(hp : p ≠ 2) (u : ZMod p) :
    ((nullConeFinset p).filter (fun w => w 2 - w 0 = u)).card = p := by sorry
