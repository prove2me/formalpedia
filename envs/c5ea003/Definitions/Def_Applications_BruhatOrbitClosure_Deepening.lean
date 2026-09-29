-- Prove2me | Definitions.Def_Applications_BruhatOrbitClosure_Deepening
-- name    : Applications_BruhatOrbitClosure_Deepening
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:38:14.489084+00:00
-- url     : https://prove2.me/theorems/41aadc1f-1b5e-47cc-a112-fbecec9e6389
-- title:
--   Aether Catalog definitions — Applications_BruhatOrbitClosure_Deepening
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.BruhatOrbitClosure.Deepening`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/BruhatOrbitClosure/Deepening.lean by skeleton subtraction
import Mathlib

/-!
# Closure relations from graph embeddings of ordered parameters

This file isolates and strengthens the order-theoretic mechanism behind two-projection
parametrisations of orbit strata.  Given a relation `r` and a self-map `ι` preserving and
reflecting it, the graph map `x ↦ (x, ι x)` embeds `r` into the componentwise product
relation.  Moreover, it identifies every principal closure with the corresponding principal
closure inside its graph image, and it transports arbitrary lower sets exactly.

For Bruhat order, the intended self-map is inversion.  Thus the results apply once inversion
invariance of Bruhat order has been established, independently of a particular geometric
realisation of the orbit set.
-/

namespace BruhatOrbitDeepening

universe u v

variable {α : Type u} {β : Type v}

/-- Componentwise extension of a relation to a product. -/
def ProductRel (r : α → α → Prop) (s : β → β → Prop) (x y : α × β) : Prop :=
  r x.1 y.1 ∧ s x.2 y.2

/-- The graph parametrisation associated to a self-map. -/
def graphParam (ι : α → α) (x : α) : α × α := (x, ι x)

/-- The principal closure (principal lower set) determined by a relation. -/
def principalClosure (r : α → α → Prop) (x : α) : Set α :=
  {y | r y x}








end BruhatOrbitDeepening


