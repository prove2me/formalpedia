-- Prove2me | Definitions.Def_arexychen_erdos180_finite
-- name    : arexychen_erdos180_finite
-- status  : Definition
-- author  : @arexychen
-- created : 2026-09-09T07:18:04.602283+00:00
-- url     : https://prove2.me/theorems/8c8cf292-b4e9-4a2e-8556-5f3861d3018d
-- title:
--   Finite simple graphs and predicates on their non-isolated parts
-- statement:
--   A finite simple graph packages a vertex type in an arbitrary universe, a finite enumeration of that type, and a simple graph on it. The bundle supplies the associated finite-type instance, the graph induced on non-isolated vertices, the original graph's extremal function, and predicates for having at least two reduced edges, being a reduced star, or being a reduced matching. Combined star/matching predicates also require at least two reduced edges.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Finite.lean#L12-L53

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- A finite graph packaged with its vertex type. -/
structure FiniteSimpleGraph where
  V : Type u
  instFintype : Fintype V
  graph : SimpleGraph V

namespace FiniteSimpleGraph

instance (X : FiniteSimpleGraph.{u}) : Fintype X.V :=
  X.instFintype

/-- The non-isolated part of a packaged graph. -/
abbrev reduced (X : FiniteSimpleGraph.{u}) : SimpleGraph X.graph.support :=
  deleteIsolated X.graph

/-- The extremal function of a packaged graph. -/
def extremal (X : FiniteSimpleGraph.{u}) (n : ℕ) : ℕ :=
  extremalNumber X.graph n



/-- The reduced graph has at least two edges. -/
def atLeastTwoEdgesAfterDeletingIsolated (X : FiniteSimpleGraph.{u}) : Prop :=
  2 ≤ edgeCount X.reduced

/-- The reduced graph is a star. -/
def starAfterDeletingIsolated (X : FiniteSimpleGraph.{u}) : Prop :=
  IsStar X.reduced

/-- The reduced graph is a matching. -/
def matchingAfterDeletingIsolated (X : FiniteSimpleGraph.{u}) : Prop :=
  IsMatchingGraph X.reduced

def starWithAtLeastTwoEdgesAfterDeletingIsolated
    (X : FiniteSimpleGraph.{u}) : Prop :=
  X.starAfterDeletingIsolated ∧ X.atLeastTwoEdgesAfterDeletingIsolated

def matchingWithAtLeastTwoEdgesAfterDeletingIsolated
    (X : FiniteSimpleGraph.{u}) : Prop :=
  X.matchingAfterDeletingIsolated ∧ X.atLeastTwoEdgesAfterDeletingIsolated

end FiniteSimpleGraph





end Erdos180

end
end Arexychen


