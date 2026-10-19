-- Prove2me | Definitions.Def_AT260939824_Nonisolated
-- name    : AT260939824_Nonisolated
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:24:22.074736+00:00
-- url     : https://prove2.me/theorems/c09446be-96f8-4913-874c-f913a90e971e
-- title:
--   The induced graph of nonisolated vertices
-- statement:
--   For a simple graph $H$ on $V$, a vertex is nonisolated when it has an adjacent vertex. The induced graph on these vertices has a total chosen-neighbor function. Given one nonisolated base vertex, all isolated vertices can be sent to that base vertex while nonisolated vertices are fixed, producing a graph homomorphism from $H$ to its nonisolated induced graph.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/Nonisolated.lean, selected declaration lines 16, 18, 20-23, 25-26, 32-40; SHA-256 7eabef2c039b4269800cd3c2a8410ff2256b69b5b26a1768f557127a894294b0. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_ReducedWalks
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

/-!
# Removing isolated target vertices

The nonisolated induced graph has a total neighbor selection.  Retraction
onto it preserves the odd torsion hypotheses of the target paper.
-/

namespace AbelianTargets

noncomputable section

variable {V : Type*} (H : SimpleGraph V)

def nonisolatedVertices : Set V := {v | ∃ w, H.Adj v w}

def NonisolatedGraph : SimpleGraph (nonisolatedVertices H) := H.induce (nonisolatedVertices H)

theorem nonisolated_neighbor (v : nonisolatedVertices H) :
    ∃ w : nonisolatedVertices H, (NonisolatedGraph H).Adj v w := by
  obtain ⟨w, hw⟩ := v.property
  exact ⟨⟨w, ⟨v.val, hw.symm⟩⟩, hw⟩

def nonisolatedNeighbor (v : nonisolatedVertices H) : nonisolatedVertices H :=
  Classical.choose (nonisolated_neighbor H v)



def nonisolatedRetraction (b : nonisolatedVertices H) : H →g NonisolatedGraph H := by
  classical
  exact {
    toFun := fun v => if hv : v ∈ nonisolatedVertices H then ⟨v, hv⟩ else b
    map_rel' := by
      intro u v huv
      have hu : u ∈ nonisolatedVertices H := ⟨v, huv⟩
      have hv : v ∈ nonisolatedVertices H := ⟨u, huv.symm⟩
      simpa only [dif_pos hu, dif_pos hv] using huv }







end

end AbelianTargets


