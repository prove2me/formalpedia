-- Prove2me | solution 1 for Arexychen.Erdos180.edgeCount_induce_compl_singleton
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:21:58.750284+00:00
-- url     : https://prove2.me/submissions/24046f8a-4f98-4f4f-a63b-34f1ecb2f788

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
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

/-- The repository's `edgeCount` agrees with mathlib's finite edge finset count. -/
private theorem edgeCount_eq_edgeFinset_card
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]












end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v

end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v
open Arexychen.Erdos180 in
/-- Edge count after deleting a single vertex, stated in repository vocabulary. -/
theorem solution
    {α : Type u} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) :
    edgeCount (G.induce ({v}ᶜ : Set α)) + G.degree v = edgeCount G := by
  classical
  have hdeg_le : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
  calc
    edgeCount (G.induce ({v}ᶜ : Set α)) + G.degree v
        = (G.induce ({v}ᶜ : Set α)).edgeFinset.card + G.degree v := by
          rw [edgeCount_eq_edgeFinset_card]
    _ = (G.deleteIncidenceSet v).edgeFinset.card + G.degree v := by
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton]
    _ = (G.edgeFinset.card - G.degree v) + G.degree v := by
          rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
    _ = G.edgeFinset.card := Nat.sub_add_cancel hdeg_le
    _ = edgeCount G := (edgeCount_eq_edgeFinset_card G).symm
end
namespace Arexychen
noncomputable section
namespace Erdos180
































-- `[Fintype α]` is unused in the statement but required by the proof
-- (the witness constant is `Fintype.card α`), hence the linter override.




-- `[Fintype α]` is unused in the statement but required by the proof
-- (it applies the guarded bound above), hence the linter override.


















end Erdos180

end
end Arexychen
