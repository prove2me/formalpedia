-- Prove2me | solution 1 for Arexychen.Erdos180.matchingConstruction_extremalFamily_eventually_half_le
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:27:50.366886+00:00
-- url     : https://prove2.me/submissions/d46a6ada-4b15-4ce9-a0e8-dd7c33026406

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_bounds
import Definitions.Def_arexychen_erdos180_families_matching
import Definitions.Def_arexychen_erdos180_finite
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic
import Theorems.Thm_Arexychen_Erdos180_edgeCount_matchingHost
import Theorems.Thm_Arexychen_Erdos180_matchingHost_isMatchingGraph

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















/-- If a graph embeds into a matching graph, then its non-isolated part is a
matching graph. -/
private theorem deleteIsolated_isMatchingGraph_of_embeds_into_isMatchingGraph
    {α : Type u} {β : Type v}
    {H : SimpleGraph α} {G : SimpleGraph β}
    (hG : IsMatchingGraph G)
    (hemb : EmbedsAsSubgraph H G) :
    IsMatchingGraph (deleteIsolated H) := by
  rcases hemb with ⟨f, hf, hmap⟩
  intro x y z hxy hxz
  apply Subtype.ext
  apply hf
  exact hG (hmap (by simpa [deleteIsolated] using hxy))
    (hmap (by simpa [deleteIsolated] using hxz))

end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
/-- Matching lower-bound construction: if no forbidden member reduces to a
matching, then a matching of size `⌊n/2⌋` is family-free on `n` vertices. -/
theorem solution
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (_hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hNoMatching : ∀ i : ι, ¬ (F i).matchingAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n / 2 ≤ extremalFamily F n := by
  refine eventually_atTop.2 ⟨0, ?_⟩
  intro n _hn
  let G : SimpleGraph (Fin n) := matchingHost n
  have hfree : FamilyFree F G := by
    intro i hemb
    exact hNoMatching i
      (deleteIsolated_isMatchingGraph_of_embeds_into_isMatchingGraph
        (matchingHost_isMatchingGraph n) hemb)
  have hhost : edgeCount G ≤ extremalFamily F n :=
    extremalFamily_ge_of_host F G hfree
  have hcount : edgeCount G = n / 2 := by
    simpa [G] using edgeCount_matchingHost n
  omega
end
namespace Arexychen
noncomputable section
namespace Erdos180


end Erdos180

end
end Arexychen
