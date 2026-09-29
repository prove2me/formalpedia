-- Prove2me | Definitions.Def_Algebra_CatalogbuildSharedSublevelFull_Sublevel_full
-- name    : Algebra_CatalogbuildSharedSublevelFull_Sublevel_full
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:08:49.393645+00:00
-- url     : https://prove2.me/theorems/466e9a88-663b-46fb-8211-9fcb0d93d14e
-- title:
--   Aether Catalog definitions — Algebra_CatalogbuildSharedSublevelFull_Sublevel_full
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.CatalogbuildSharedSublevelFull.Sublevel.full`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/CatalogbuildSharedSublevelFull/Sublevel_full.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Sublevel_full

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 5

Repaired: the statistic `E` used by `sublevel` is defined here.
-/

/-- The remainder statistic `E N x = N % x` on which the sublevel sets are
based (it was used but never declared in the generated file). -/
def E (N x : ℕ) : ℕ := N % x

/-- The sublevel set of the remainder statistic. -/
def sublevel (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


