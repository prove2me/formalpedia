-- Prove2me | Definitions.Def_Combinatorics_ErdosFaberLovasz
-- name    : Combinatorics_ErdosFaberLovasz
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:24:43.712278+00:00
-- url     : https://prove2.me/theorems/76e6e6eb-bc0d-4fa8-981d-71c2b7da3985
-- title:
--   Aether Catalog definitions — Combinatorics_ErdosFaberLovasz
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.ErdosFaberLovasz`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/ErdosFaberLovasz.lean by skeleton subtraction
import Mathlib

open Finset

namespace ErdosFaberLovasz

variable {V : Type*} [DecidableEq V]

/-- A finite hypergraph is represented by its finite set of finite edges. -/
abbrev Hypergraph (V : Type*) [DecidableEq V] := Finset (Finset V)

/-- Every edge of an `r`-uniform hypergraph has exactly `r` vertices. -/
def IsUniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A hypergraph is linear when two different edges share at most one vertex. -/
def IsLinear (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1

/-- A hypergraph is intersecting when every two of its edges meet. -/
def IsIntersecting (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, (e ∩ f).Nonempty

/-- A coloring is proper for the clique-union graph when every hyperedge is rainbow:
distinct vertices in one edge receive distinct colors. -/
def IsProperColoring (H : Hypergraph V) {k : ℕ} (color : V → Fin k) : Prop :=
  ∀ e ∈ H, ∀ x ∈ e, ∀ y ∈ e, x ≠ y → color x ≠ color y









end ErdosFaberLovasz


