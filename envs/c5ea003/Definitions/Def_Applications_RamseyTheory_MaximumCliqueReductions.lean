-- Prove2me | Definitions.Def_Applications_RamseyTheory_MaximumCliqueReductions
-- name    : Applications_RamseyTheory_MaximumCliqueReductions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:42.56496+00:00
-- url     : https://prove2.me/theorems/31551aac-884e-40da-b069-d968171e0902
-- title:
--   Aether Catalog definitions — Applications_RamseyTheory_MaximumCliqueReductions
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.RamseyTheory.MaximumCliqueReductions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/RamseyTheory/MaximumCliqueReductions.lean by skeleton subtraction
import Mathlib

/-!
# Upper-bound-driven reductions for maximum clique

This file isolates the mathematical core of upper-bound-enhanced core and truss
reductions. An upper-bound oracle is treated extensionally: on every vertex set
it bounds the cardinality of every finite clique contained there. The results
show that a clique can contain a proposed pattern only when the oracle value on
its common neighborhood is large enough, and that repeated certified vertex
peeling preserves every clique above the target size.
-/

open Set

namespace MaximumCliqueReductions

variable {V : Type*} (G : SimpleGraph V)

/-- A set of vertices is a clique when every two distinct members are adjacent. -/
def IsClique (C : Set V) : Prop := C.Pairwise G.Adj

/-- The vertices adjacent to every vertex of `D`. -/
def commonNeighbors (D : Set V) : Set V := {v | ∀ w ∈ D, G.Adj v w}

/-- An extensional upper-bound oracle for clique size on each vertex set. -/
def IsCliqueUpperBound (ub : Set V → ℕ) : Prop :=
  ∀ S C : Set V, C.Finite → IsClique G C → C ⊆ S → C.ncard ≤ ub S






/-- A certified core-peeling step deletes one vertex whose neighborhood upper
bound is too small to support a clique of the target size. -/
def CoreStep (ub : Set V → ℕ) (k : ℕ) (S T : Set V) : Prop :=
  ∃ v ∈ S, 1 + ub (S ∩ commonNeighbors G {v}) < k ∧ T = S \ {v}



end MaximumCliqueReductions


