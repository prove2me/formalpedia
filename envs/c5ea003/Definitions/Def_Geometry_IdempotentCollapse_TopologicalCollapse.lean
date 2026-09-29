-- Prove2me | Definitions.Def_Geometry_IdempotentCollapse_TopologicalCollapse
-- name    : Geometry_IdempotentCollapse_TopologicalCollapse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:05.896981+00:00
-- url     : https://prove2.me/theorems/ebf99df0-b4c0-4857-b1af-27f298e1e352
-- title:
--   Aether Catalog definitions — Geometry_IdempotentCollapse_TopologicalCollapse
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.IdempotentCollapse.TopologicalCollapse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/IdempotentCollapse/TopologicalCollapse.lean by skeleton subtraction
import Mathlib

open Set

/-! # CatalogBuild.Speculative.IdempotentCollapse.TopologicalCollapse

Auto-generated from theorem catalog database.
Domain: Speculative/IdempotentCollapse
Declarations: 8
-/

/-- A retraction onto a subset. -/
structure Retraction' (α : Type*) (S : Set α) where
  map : α → α
  maps_into : ∀ x, map x ∈ S
  fixes_S : ∀ x ∈ S, map x = x





/-- The fiber of a map over a point. -/
def retraction_fiber' {α : Type*} (f : α → α) (y : α) : Set α := {x | f x = y}


