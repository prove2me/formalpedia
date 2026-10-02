-- Prove2me | solution 1 for Arexychen.Erdos180.oneEdgeConstruction_extremalFamily_eventually_one_le
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:38:49.573639+00:00
-- url     : https://prove2.me/submissions/4f18393a-8063-4317-b193-8a3b8c706d8b

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_bounds
import Definitions.Def_arexychen_erdos180_families_oneedge
import Definitions.Def_arexychen_erdos180_finite
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic
import Theorems.Thm_Arexychen_Erdos180_edgeCount_deleteIsolated_le_of_embeds
import Theorems.Thm_Arexychen_Erdos180_edgeCount_oneEdgeHost

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



/-- No graph whose non-isolated part has at least two edges embeds into a
host with at most one edge. -/
private theorem isHFree_of_two_deleteIsolated_edges_of_edgeCount_le_one
    {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β)
    [Finite G.edgeSet]
    (hTwo : 2 ≤ edgeCount (deleteIsolated H))
    (hG : edgeCount G ≤ 1) :
    IsHFree H G := by
  intro hemb
  have hle : edgeCount (deleteIsolated H) ≤ edgeCount G :=
    edgeCount_deleteIsolated_le_of_embeds H G hemb
  omega





end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
/-- Single-edge lower-bound construction: if every forbidden graph has at
least two non-isolated edges, then the one-edge host is admissible for all large
`n`, so the family extremal function is eventually at least one. -/
theorem solution
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hTwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated) :
    ∀ᶠ n in atTop, 1 ≤ extremalFamily F n := by
  refine eventually_atTop.2 ⟨2, ?_⟩
  intro n hn
  let G : SimpleGraph (Fin n) := oneEdgeHost n hn
  have hfree : FamilyFree F G := by
    intro i
    classical
    letI : Finite G.edgeSet := inferInstance
    exact isHFree_of_two_deleteIsolated_edges_of_edgeCount_le_one
      (F i).graph G (hTwo i) (by
        rw [edgeCount_oneEdgeHost hn])
  have hhost : edgeCount G ≤ extremalFamily F n :=
    extremalFamily_ge_of_host F G hfree
  have hone : edgeCount G = 1 := edgeCount_oneEdgeHost hn
  omega
end
namespace Arexychen
noncomputable section
namespace Erdos180


end Erdos180

end
end Arexychen
