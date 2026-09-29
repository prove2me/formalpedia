-- Prove2me | Definitions.Def_Algebra_IntegerEnergy_UniversalPhotonMap
-- name    : Algebra_IntegerEnergy_UniversalPhotonMap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:21:08.740321+00:00
-- url     : https://prove2.me/theorems/968c2f58-2d0e-4ced-bc16-7b6d524449c8
-- title:
--   Aether Catalog definitions — Algebra_IntegerEnergy_UniversalPhotonMap
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.IntegerEnergy.UniversalPhotonMap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/IntegerEnergy/UniversalPhotonMap.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Logic.UniversalPhotonMap

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 26
-/

noncomputable section

/-- A vertex in the photon graph: a spacetime event. -/
structure PhotonVertex where
  x : ℤ
  y : ℤ
  t : ℤ
  deriving DecidableEq, Repr

/-- A directed edge: a photon worldline from emission to absorption. -/
structure PhotonArc where
  source : PhotonVertex
  target : PhotonVertex
  null_condition : (target.x - source.x)^2 + (target.y - source.y)^2 =
                   (target.t - source.t)^2
  causal : source.t < target.t

/-- The universal photon graph. -/
structure PhotonGraph where
  vertices : Finset PhotonVertex
  arcs : Finset PhotonArc
  source_mem : ∀ a ∈ arcs, a.source ∈ vertices
  target_mem : ∀ a ∈ arcs, a.target ∈ vertices


/-- A photon path: a sequence of connected arcs. -/
inductive PhotonPath : PhotonVertex → PhotonVertex → Prop where
  | single (a : PhotonArc) : PhotonPath a.source a.target
  | cons (a : PhotonArc) {v : PhotonVertex}
    (rest : PhotonPath a.target v) : PhotonPath a.source v






/-- The state at a time slice: all active photons. -/
def PhotonGraph.stateAtTime (G : PhotonGraph) (time : ℤ) : Finset PhotonArc :=
  G.arcs.filter (fun a => a.source.t ≤ time ∧ time < a.target.t)


/-- Two photons are adjacent if they share a spacetime event. -/
def photonsAdjacent (a₁ a₂ : PhotonArc) : Prop :=
  a₁.target = a₂.source ∨ a₂.target = a₁.source

/-- Adjacency is symmetric. -/
theorem photonsAdjacent_symm (a₁ a₂ : PhotonArc) :
    photonsAdjacent a₁ a₂ → photonsAdjacent a₂ a₁ := by
  intro h; rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The undirected photon graph. -/
structure UndirectedPhotonGraph where
  photons : Finset PhotonArc
  adj : PhotonArc → PhotonArc → Prop
  adj_symm : ∀ a₁ a₂, adj a₁ a₂ → adj a₂ a₁

/-- Convert directed → undirected. -/
def PhotonGraph.toUndirected (G : PhotonGraph) : UndirectedPhotonGraph where
  photons := G.arcs
  adj := photonsAdjacent
  adj_symm := photonsAdjacent_symm

/-- Reachability in the undirected graph. -/
inductive UndirectedReachable (G : UndirectedPhotonGraph) :
    PhotonArc → PhotonArc → Prop where
  | refl (a : PhotonArc) : UndirectedReachable G a a
  | step (a b c : PhotonArc) :
    a ∈ G.photons → b ∈ G.photons →
    G.adj a b → UndirectedReachable G b c → UndirectedReachable G a c


/-- A connected photon graph: all photons can reach each other. -/
def PhotonGraph.isConnected (G : PhotonGraph) : Prop :=
  ∀ a₁ a₂, a₁ ∈ G.arcs → a₂ ∈ G.arcs →
    UndirectedReachable G.toUndirected a₁ a₂





/-- A photon graph is in equilibrium if the state is constant. -/
def PhotonGraph.inEquilibrium (G : PhotonGraph) (t₁ t₂ : ℤ) : Prop :=
  G.stateAtTime t₁ = G.stateAtTime t₂



end


