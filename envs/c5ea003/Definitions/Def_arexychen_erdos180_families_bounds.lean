-- Prove2me | Definitions.Def_arexychen_erdos180_families_bounds
-- name    : arexychen_erdos180_families_bounds
-- status  : Definition
-- author  : @arexychen
-- created : 2026-09-09T07:18:21.876582+00:00
-- url     : https://prove2.me/theorems/c9f24aef-5446-44ad-a060-8878116f54b6
-- title:
--   Indexed forbidden families and the star–matching pair predicate
-- statement:
--   For an indexed family $F$, family freeness means that every member is absent as an ordinary subgraph of the host. For finite index types, the family extremal function is the natural supremum of edge counts of family-free graphs on $\operatorname{Fin}(n)$. The pair predicate asserts existence of an index with a reduced star of at least two edges and an index with a reduced matching of at least two edges. It does not add a distinct-index hypothesis or replace the indexed family with a finite set.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Bounds.lean#L71-L157

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_finite
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

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v w





/-- A host graph avoids every member of a finite indexed family. -/
def FamilyFree {ι : Type v}
    (F : ι → FiniteSimpleGraph.{u})
    {W : Type w}
    (G : SimpleGraph W) : Prop :=
  ∀ i : ι, IsHFree (F i).graph G

/-- The extremal number for a finite indexed family of forbidden graphs. -/
def extremalFamily {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), FamilyFree F G ∧ edgeCount G = m}









/-- The family contains both a star and a matching, each with at least two edges
after deleting isolated vertices. -/
def FamilyContainsStarMatchingPair {ι : Type v}
    (F : ι → FiniteSimpleGraph.{u}) : Prop :=
  (∃ i : ι, (F i).starWithAtLeastTwoEdgesAfterDeletingIsolated) ∧
    (∃ j : ι, (F j).matchingWithAtLeastTwoEdgesAfterDeletingIsolated)

end Erdos180

end
end Arexychen


