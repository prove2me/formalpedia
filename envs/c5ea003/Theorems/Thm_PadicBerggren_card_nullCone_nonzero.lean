-- Prove2me | Theorems.Thm_PadicBerggren_card_nullCone_nonzero
-- name    : PadicBerggren.card_nullCone_nonzero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:34:58.920647+00:00
-- url     : https://prove2.me/theorems/595eaafd-9ac0-40a6-aaa5-5dd25322fc1a
-- title:
--   `p² − 1` nonzero null vectors.
-- statement:
--   **`p² − 1` nonzero null vectors.**  Since every Berggren move is linear and fixes `0`,
--   the interesting part of the phase space has exactly `p² − 1` points; as the moves commute with
--   scaling this is `p + 1` projective null points, each with `p − 1` representatives.
--
--   ```lean
--   theorem PadicBerggren.card_nullCone_nonzero(hp : p ≠ 2) :
--       ((nullConeFinset p).erase 0).card = p ^ 2 - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PadicBerggrenNullCone.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PadicBerggrenNullCone.lean#L133

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

theorem PadicBerggren.card_nullCone_nonzero(hp : p ≠ 2) :
    ((nullConeFinset p).erase 0).card = p ^ 2 - 1 := by sorry
