-- Prove2me | Definitions.Def_Logic_RootedPathIrregularity_Contrarian
-- name    : Logic_RootedPathIrregularity_Contrarian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:33.461733+00:00
-- url     : https://prove2.me/theorems/6114a429-0fb5-40e0-a2c7-a570e0282f37
-- title:
--   Aether Catalog definitions — Logic_RootedPathIrregularity_Contrarian
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.RootedPathIrregularity.Contrarian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/RootedPathIrregularity/Contrarian.lean by skeleton subtraction
import Mathlib

/-!
# Contrarian results on rooted three-vertex paths

This file isolates the local counting mechanism behind the exceptional case `P₃`.
It also gives a certified six-vertex counterexample to the tempting conjecture that
ordinary `P₃`-irregularity forces end-rooted `P₃`-irregularity.
-/

namespace RootedPathIrregularity

/-- A finite loopless undirected graph, represented by a Boolean adjacency test. -/
structure FinGraph (V : Type*) [Fintype V] where
  adj : V → V → Bool
  symm : ∀ v w, adj v w = adj w v
  loopless : ∀ v, adj v v = false

namespace FinGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The neighbors of a vertex. -/
def neighbors (G : FinGraph V) (v : V) : Finset V :=
  Finset.univ.filter fun w => G.adj v w

/-- Vertex degree. -/
def degree (G : FinGraph V) (v : V) : ℕ := (G.neighbors v).card

/-- Number of copies of `P₃` in which `v` is the central root. -/
def centerP3Count (G : FinGraph V) (v : V) : ℕ := (G.degree v).choose 2

/-- Number of copies of `P₃` in which `v` is a specified end root. -/
def endP3Count (G : FinGraph V) (v : V) : ℕ :=
  ∑ w ∈ G.neighbors v, (G.degree w - 1)

/-- Number of unrooted copies of `P₃` containing `v`. -/
def ordinaryP3Count (G : FinGraph V) (v : V) : ℕ :=
  G.centerP3Count v + G.endP3Count v

/-- A vertex statistic separates every pair of vertices. -/
def Irregular (f : V → ℕ) : Prop := Function.Injective f





/-
Every finite simple graph with at least two vertices has two vertices of equal degree.
-/

/-
The central-root count for `P₃` can never distinguish all vertices of a
nontrivial finite graph.  This strengthens the paper's negative observation by
making the degree-collision obstruction explicit.
-/

end FinGraph

section Counterexample

/-- The graph with edges `02, 03, 05, 12, 14, 23`. -/
def sixVertexGraph : FinGraph (Fin 6) where
  adj v w :=
    (v = 0 && w = 2) || (v = 2 && w = 0) ||
    (v = 0 && w = 3) || (v = 3 && w = 0) ||
    (v = 0 && w = 5) || (v = 5 && w = 0) ||
    (v = 1 && w = 2) || (v = 2 && w = 1) ||
    (v = 1 && w = 4) || (v = 4 && w = 1) ||
    (v = 2 && w = 3) || (v = 3 && w = 2)
  symm := by decide
  loopless := by decide




end Counterexample

end RootedPathIrregularity


