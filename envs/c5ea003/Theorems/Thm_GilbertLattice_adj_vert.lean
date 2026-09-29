-- Prove2me | Theorems.Thm_GilbertLattice_adj_vert
-- name    : GilbertLattice.adj_vert
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:24:43.45079+00:00
-- url     : https://prove2.me/theorems/a8ae186a-5742-4dc5-baf6-2519faa30364
-- title:
--   Adj vert
-- statement:
--   Formal statement of `GilbertLattice.adj_vert` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GilbertLattice.adj_vert(hR : Real.sqrt 5 < R) (i j : ℤ) :
--       (gilbert R C).Adj (i, j) (i, j + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeConnectivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeConnectivity.lean#L45

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

theorem GilbertLattice.adj_vert(hR : Real.sqrt 5 < R) (i j : ℤ) :
    (gilbert R C).Adj (i, j) (i, j + 1) := by sorry
