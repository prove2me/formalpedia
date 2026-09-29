-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedSublevelFull_Sublevel_full
-- name    : Shared_CatalogbuildSharedSublevelFull_Sublevel_full
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:39.002851+00:00
-- url     : https://prove2.me/theorems/c9334f51-48c3-4fed-8794-a8ecf3a89f38
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedSublevelFull_Sublevel_full
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedSublevelFull.Sublevel.full`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedSublevelFull/Sublevel_full.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_CatalogbuildSharedE_E

/-! # CatalogBuild.Shared.Sublevel_full

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 5

Repaired: the `import` lines now head the file and the definition `sublevel`
precedes the statements that use it (the underlying energy function `E` lives in
`Shared.CatalogbuildSharedE.E`).
-/


def sublevel (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


