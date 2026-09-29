-- Prove2me | Theorems.Thm_berggrenAt_pyth
-- name    : berggrenAt_pyth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:06:13.587893+00:00
-- url     : https://prove2.me/theorems/f2616315-4f31-4614-b8f0-f414c6a66318
-- title:
--   Every position in the Berggren tree yields a Pythagorean triple.
-- statement:
--   Every position in the Berggren tree yields a Pythagorean triple.
--
--   ```lean
--   theorem berggrenAt_pyth(path : BPos) :
--       let (a, b, c) := berggrenAt path
--       a ^ 2 + b ^ 2 = c ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/BerggrenRamanujan.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/BerggrenRamanujan.lean#L42

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

theorem berggrenAt_pyth(path : BPos) :
    let (a, b, c) := berggrenAt path
    a ^ 2 + b ^ 2 = c ^ 2 := by sorry
