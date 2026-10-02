-- Prove2me | solution 1 for Arexychen.Erdos180.exists_degree_one_of_isAcyclic_of_edge
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:20:43.802998+00:00
-- url     : https://prove2.me/submissions/46cd674d-97a3-482d-8e60-5b93709007ee

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

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v









private theorem component_nontrivial_of_adj
    {α : Type u} {F : SimpleGraph α} {x y : α} (hxy : F.Adj x y) :
    Nontrivial (F.connectedComponentMk x) := by
  refine ⟨⟨⟨x, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩,
    ⟨y, ?_⟩, ?_⟩⟩
  · exact (F.connectedComponentMk x).mem_supp_of_adj_mem_supp
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem hxy
  · intro h
    exact hxy.ne (congrArg Subtype.val h)

end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v
open Arexychen.Erdos180 in
/-- A finite acyclic graph with an edge has a vertex of degree one. -/
theorem solution
    {α : Type u} [Fintype α] (F : SimpleGraph α) [DecidableRel F.Adj]
    (hF : F.IsAcyclic) (hedge : F.edgeFinset.Nonempty) :
    ∃ v : α, F.degree v = 1 := by
  classical
  have hne : F ≠ ⊥ := SimpleGraph.edgeFinset_nonempty.mp hedge
  rcases SimpleGraph.ne_bot_iff_exists_adj.mp hne with ⟨x, y, hxy⟩
  let C : F.ConnectedComponent := F.connectedComponentMk x
  haveI : Nontrivial C := component_nontrivial_of_adj hxy
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have htree : C.toSimpleGraph.IsTree := hF.isTree_connectedComponent C
  rcases htree.exists_vert_degree_one_of_nontrivial with ⟨v, hv⟩
  have hcomp_unique : ∃! u : C, C.toSimpleGraph.Adj v u :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj
      (G := C.toSimpleGraph) (v := v)).mp hv
  rcases hcomp_unique with ⟨u, hvu, huniq⟩
  have hamb_unique : ∃! u : α, F.Adj v u := by
    refine ⟨u, ?_, ?_⟩
    · simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hvu
    · intro w hvw
      have hwC : w ∈ C :=
        (C.mem_supp_congr_adj hvw).mp v.property
      have hcw : C.toSimpleGraph.Adj v ⟨w, hwC⟩ := by
        simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hvw
      exact congrArg Subtype.val (huniq ⟨w, hwC⟩ hcw)
  exact ⟨v, (SimpleGraph.degree_eq_one_iff_existsUnique_adj
    (G := F) (v := (v : α))).mpr hamb_unique⟩
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
