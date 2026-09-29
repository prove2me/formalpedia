-- Prove2me | Theorems.Thm_GilbertLattice_adj_horiz
-- name    : GilbertLattice.adj_horiz
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:25:01.910011+00:00
-- url     : https://prove2.me/theorems/843c7b4b-c55c-4b88-843a-dc850f8b1d6b
-- title:
--   Adj horiz
-- statement:
--   Formal statement of `GilbertLattice.adj_horiz` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GilbertLattice.adj_horiz(hR : Real.sqrt 5 < R) (i j : ℤ) :
--       (gilbert R C).Adj (i, j) (i + 1, j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeConnectivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeConnectivity.lean#L28

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

theorem GilbertLattice.adj_horiz(hR : Real.sqrt 5 < R) (i j : ℤ) :
    (gilbert R C).Adj (i, j) (i + 1, j) := by sorry
