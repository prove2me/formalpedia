-- Prove2me | Definitions.Def_Bridges_CliqueUpperBoundReductions
-- name    : Bridges_CliqueUpperBoundReductions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:31.794122+00:00
-- url     : https://prove2.me/theorems/df7ba78c-0167-4a2d-a63c-9d5c6de74b26
-- title:
--   Aether Catalog definitions — Bridges_CliqueUpperBoundReductions
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CliqueUpperBoundReductions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CliqueUpperBoundReductions.lean by skeleton subtraction
import Mathlib

open Finset

namespace CliqueUpperBoundReductions

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An upper-bound function is valid when it bounds every clique contained in the
queried vertex set. No monotonicity or computability assumption is needed. -/
def UpperBoundValid (G : SimpleGraph V) (upper : Finset V → ℕ) : Prop :=
  ∀ ⦃S C : Finset V⦄, C ⊆ S → G.IsClique (C : Set V) → C.card ≤ upper S

/-- Vertices adjacent to every vertex of a finite seed. -/
noncomputable def commonNeighbors (G : SimpleGraph V) (D : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ ∀ d ∈ D, G.Adj v d

/-- The upper-bound reduction test attached to a seed `D`. -/
def SeedReducible (G : SimpleGraph V) (upper : Finset V → ℕ)
    (k : ℕ) (D : Finset V) : Prop :=
  D.card + upper (commonNeighbors G D) ≤ k







end CliqueUpperBoundReductions


