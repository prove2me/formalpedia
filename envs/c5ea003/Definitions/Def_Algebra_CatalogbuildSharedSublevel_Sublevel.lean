-- Prove2me | Definitions.Def_Algebra_CatalogbuildSharedSublevel_Sublevel
-- name    : Algebra_CatalogbuildSharedSublevel_Sublevel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:08:51.229364+00:00
-- url     : https://prove2.me/theorems/94f1120c-8704-4357-96df-a6a4eb71f786
-- title:
--   Aether Catalog definitions — Algebra_CatalogbuildSharedSublevel_Sublevel
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.CatalogbuildSharedSublevel.Sublevel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/CatalogbuildSharedSublevel/Sublevel.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Sublevel

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5

Repaired: the statistic `E` used by `sublevel` is defined here.
-/

/-- The remainder statistic `E N x = N % x` on which the sublevel sets are
based (it was used but never declared in the generated file). -/
def E (N x : ℕ) : ℕ := N % x

/-- The sublevel set of the remainder statistic. -/
def sublevel (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


