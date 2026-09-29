-- Prove2me | Theorems.Thm_GilbertLattice_connected_of_sqrt_five_lt
-- name    : GilbertLattice.connected_of_sqrt_five_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:36:55.931116+00:00
-- url     : https://prove2.me/theorems/2803fd21-012f-4053-a034-16aee57a220c
-- title:
--   All points are connected above `â5`.
-- statement:
--   **All points are connected above `â5`.**  For every radius `R > â5` and every
--   placement of the points, the Gilbert graph is connected: any two points of the plane
--   are joined by a chain of points at mutual distance `< R`.
--
--   ```lean
--   theorem GilbertLattice.connected_of_sqrt_five_lt(hR : Real.sqrt 5 < R) : (gilbert R C).Connected := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeConnectivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeConnectivity.lean#L61

-- Thm stub generated from Shared/GilbertLatticeConnectivity.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2

/-!
# Full connectivity of the conditioned Gilbert model for large radii

The third critical radius of the model is

`R_full = inf {R : for every placement of the points, all points are connected}`.

Two points sitting in two cells sharing an edge are at distance at most
`√(2² + 1²) = √5`, whatever the placement.  Consequently, as soon as `R > √5`, every
placement produces a graph containing the whole nearest-neighbour grid graph of `ℤ²`,
which is connected.  This gives `R_full ≤ √5`; the companion file
`GilbertLatticeConstructions.lean` provides the lower bound `R_full ≥ √17 / 2`.
-/

open GilbertLattice

variable {R : ℝ} (C : Config)

theorem GilbertLattice.connected_of_sqrt_five_lt(hR : Real.sqrt 5 < R) : (gilbert R C).Connected := by sorry
