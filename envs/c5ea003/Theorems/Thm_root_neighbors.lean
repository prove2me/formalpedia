-- Prove2me | Theorems.Thm_root_neighbors
-- name    : root_neighbors
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:06:37.037668+00:00
-- url     : https://prove2.me/theorems/70d7ef77-da32-43a9-bf8a-80caf091b34b
-- title:
--   The root has exactly 3 neighbors.
-- statement:
--   The root has exactly 3 neighbors.
--
--   ```lean
--   theorem root_neighbors:
--       {q : BPos | berggrenAdj [] q} = {[BDir.left], [BDir.mid], [BDir.right]} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/BerggrenRamanujan.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/BerggrenRamanujan.lean#L207

-- Thm stub generated from Geometry/BerggrenRamanujan.lean
import Mathlib
import Definitions.Def_Geometry_BerggrenRamanujan

open Matrix

/-! # CatalogBuild.Pythagorean.Berggren.BerggrenRamanujan

Auto-generated from theorem catalog database.
Domain: Pythagorean/Berggren
Declarations: 59
-/

noncomputable section

theorem root_neighbors:
    {q : BPos | berggrenAdj [] q} = {[BDir.left], [BDir.mid], [BDir.right]} := by sorry
