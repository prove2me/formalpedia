-- Prove2me | solution 1 for Arexychen.Erdos180.starConstruction_extremalFamily_eventually_pred_le
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:29:55.972446+00:00
-- url     : https://prove2.me/submissions/742988bb-d898-4d57-821b-1fd6d3450198

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_bounds
import Definitions.Def_arexychen_erdos180_finite
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic
import Theorems.Thm_Arexychen_Erdos180_deleteIsolated_isStar_of_embeds_into_star
import Theorems.Thm_Arexychen_Erdos180_edgeCount_starGraph_fin

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





/-- Membership in a bounded set of natural numbers gives a lower bound on its
supremum. -/
private theorem nat_le_sSup_of_mem_of_forall_le {s : Set ℕ} {m C : ℕ}
    (hm : m ∈ s)
    (hC : ∀ x ∈ s, x ≤ C) :
    m ≤ sSup s := by
  exact le_csSup ⟨C, hC⟩ hm

/-- A graph on `n` labelled vertices has at most `n.choose 2` edges. -/
private theorem edgeCount_le_complete_bound {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    edgeCount G ≤ n.choose 2 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hedge : edgeCount G = G.edgeFinset.card :=
    edgeCount_eq_edgeFinset_card G
  rw [hedge]
  simpa using (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))




end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w



/--
A positive edge count produces an adjacent pair.
-/
private theorem exists_adj_of_edgeCount_pos
    {V : Type u} (G : SimpleGraph V) [Finite G.edgeSet]
    (hpos : 0 < edgeCount G) :
    ∃ x y : V, G.Adj x y := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  rw [edgeCount, Nat.card_eq_fintype_card] at hpos
  rcases Fintype.card_pos_iff.mp hpos with ⟨e⟩
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using he
      exact ⟨x, y, hxy⟩


end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v w















/-- Any admissible host contributes a lower bound to the family extremal
number. -/
private theorem extremalFamily_ge_of_host
    {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) {n : ℕ}
    (G : SimpleGraph (Fin n))
    (hfree : FamilyFree F G) :
    edgeCount G ≤ extremalFamily F n := by
  unfold extremalFamily
  refine nat_le_sSup_of_mem_of_forall_le (C := n.choose 2) ?_ ?_
  · exact ⟨G, hfree, rfl⟩
  · intro m hm
    rcases hm with ⟨G', _hfree, rfl⟩
    exact edgeCount_le_complete_bound G'



end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w





end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
/-- Star lower-bound construction: if no forbidden member reduces to a star,
then the `n`-vertex star is family-free and has `n - 1` edges. -/
theorem solution
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hNoStar : ∀ i : ι, ¬ (F i).starAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n - 1 ≤ extremalFamily F n := by
  refine eventually_atTop.2 ⟨1, ?_⟩
  intro n hn
  classical
  have hnpos : 0 < n := Nat.succ_le_iff.mp hn
  let c : Fin n := ⟨0, hnpos⟩
  let G : SimpleGraph (Fin n) := starGraph c
  have hfree : FamilyFree F G := by
    intro i hemb
    have hpos : 0 < edgeCount (deleteIsolated (F i).graph) := by
      have htwo_i : 2 ≤ edgeCount (deleteIsolated (F i).graph) := hTwo i
      omega
    rcases exists_adj_of_edgeCount_pos (deleteIsolated (F i).graph) hpos with
      ⟨x, y, hxy⟩
    have hraw : ∃ x y : (F i).V, (F i).graph.Adj x y := by
      exact ⟨x.1, y.1, by simpa [deleteIsolated] using hxy⟩
    exact hNoStar i
      (deleteIsolated_isStar_of_embeds_into_star
        (H := (F i).graph) (c := c) hemb hraw)
  have hhost : edgeCount G ≤ extremalFamily F n :=
    extremalFamily_ge_of_host F G hfree
  have hcount : edgeCount G = n - 1 := by
    simpa [G, c] using edgeCount_starGraph_fin (n := n) hn
  omega
end
namespace Arexychen
noncomputable section
namespace Erdos180


end Erdos180

end
end Arexychen
