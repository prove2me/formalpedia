-- Prove2me | Definitions.Def_Combinatorics_Percolation
-- name    : Combinatorics_Percolation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:44:42.888418+00:00
-- url     : https://prove2.me/theorems/37d730ff-47c9-42a4-9a56-c2f71d7ca007
-- title:
--   Aether Catalog definitions — Combinatorics_Percolation
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.Percolation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/Percolation.lean by skeleton subtraction
import Mathlib
/-
# Percolation on Finite Graphs

Definitions of site and bond percolation on finite graphs,
connectivity in percolation configurations, and
monotonicity of connection probabilities.

## Main definitions
- `SiteConfig`: Boolean site configuration
- `siteConnected`: connectivity predicate in site percolation
- `BondConfig`: Boolean bond configuration
- `bondConnected`: connectivity predicate in bond percolation

## Main theorems
- `siteConnected_increasing`: site connectivity is an increasing event
- `bondConnected_increasing`: bond connectivity is an increasing event
-/


open SimpleGraph Finset

/-- A site percolation configuration assigns open/closed to each vertex. -/
abbrev SiteConfig (V : Type*) := V → Bool

/-- A bond percolation configuration assigns open/closed to each edge.
    We use `Sym2 V → Bool` and only care about values on actual edges. -/
abbrev BondConfig (V : Type*) := Sym2 V → Bool

/-- A path in a site percolation configuration: a sequence of adjacent vertices,
    all of which are open. The path connects u to v if it starts at u and ends at v,
    with all intermediate vertices open. -/
def SiteConnected {V : Type*} (G : SimpleGraph V) (η : SiteConfig V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ w ∈ p.support, η w = true

/-
Site connectivity is an increasing event: if η ≤ ξ pointwise and
    u,v are connected in η, then they are connected in ξ.
-/

/-- A path in bond percolation: a walk from u to v using only open edges. -/
def BondConnected {V : Type*} (G : SimpleGraph V) (ω : BondConfig V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ e ∈ p.edges, ω e = true

/-
Bond connectivity is an increasing event.
-/

/-- The grid graph on Fin n × Fin n with nearest-neighbor adjacency. -/
def gridGraph (n : ℕ) : SimpleGraph (Fin n × Fin n) where
  Adj u v := (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
              (u.2 = v.2 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val))
  symm u v h := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1.symm, h2.symm⟩
    · right; exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun v h => by rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega⟩

/-- A horizontal crossing of an n×n grid: a path from the left column to the right column
    through open sites. -/
def HasHorizontalCrossing (n : ℕ) (hn : 0 < n) (η : SiteConfig (Fin n × Fin n)) : Prop :=
  ∃ (a b : Fin n),
    SiteConnected (gridGraph n) η (⟨0, by omega⟩, a) (⟨⟨n - 1, by omega⟩, b⟩)

/-
Horizontal crossing is an increasing event.
-/


