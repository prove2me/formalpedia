-- Prove2me | solution 1 for Arexychen.Erdos180.familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:35:42.777667+00:00
-- url     : https://prove2.me/submissions/9808ccd1-6964-434e-9588-8898c6b64015

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
import Theorems.Thm_Arexychen_Erdos180_embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
import Theorems.Thm_Arexychen_Erdos180_exists_maximalMatching_edgeCover
import Theorems.Thm_Arexychen_Erdos180_matching_embedding_of_edgeFinset_card_ge

namespace Arexychen




open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w













/-- Subgraph embeddings compose. -/
private theorem EmbedsAsSubgraph.trans
    {α : Type u} {β : Type v} {γ : Type w}
    {H : SimpleGraph α} {G : SimpleGraph β} {K : SimpleGraph γ}
    (hHG : EmbedsAsSubgraph H G) (hGK : EmbedsAsSubgraph G K) :
    EmbedsAsSubgraph H K := by
  rcases hHG with ⟨f, hf, hfmap⟩
  rcases hGK with ⟨g, hg, hgmap⟩
  exact ⟨g ∘ f, hg.comp hf, fun _ _ hxy => hgmap (hfmap hxy)⟩

















end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w







set_option linter.unusedFintypeInType false in
/-- A matching saturates exactly twice as many vertices as it has edges.

`[Fintype V]` is unused in the statement but required by the proof
(instance synthesis for `Subgraph.finiteAt`), hence the linter override. -/
private theorem matching_verts_toFinset_card_eq_two_mul_edgeFinset_card
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (M : G.Subgraph) [DecidableRel M.Adj] [Fintype M.verts]
    (hM : M.IsMatching) :
    M.verts.toFinset.card = 2 * M.coe.edgeFinset.card := by
  classical
  rw [← M.coe.sum_degrees_eq_twice_card_edges]
  have hdeg_one :
      ∀ x : M.verts,
        @SimpleGraph.Subgraph.degree V G M (x : V) (SimpleGraph.Subgraph.finiteAt x) = 1 := by
    intro x
    rw [SimpleGraph.Subgraph.degree_eq_one_iff_existsUnique_adj]
    exact hM x.property
  simp [hdeg_one]

end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
/--
Matching-bound extraction from a forbidden matching.  If `F j`, after deleting
isolated vertices, is a matching, then an `F`-free host graph has a vertex cover
of bounded size.

Combinatorially, take a maximal matching `M` in the host.  If an edge missed
`V(M)`, then `M` was not maximal.  If `V(M)` were too large, then the forbidden
matching member of the family would embed.
-/
theorem solution
    {ι : Type v} [Finite ι] {F : ι → FiniteSimpleGraph.{u}}
    {j : ι}
    (hmatching : (F j).matchingWithAtLeastTwoEdgesAfterDeletingIsolated)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hfree : FamilyFree F G) :
    ∃ T : Finset (Fin n),
      T.card ≤ 2 * (Fintype.card (F j).V - 1) ∧
        ∀ ⦃x y : Fin n⦄, G.Adj x y → x ∈ T ∨ y ∈ T := by
  classical
  rcases exists_maximalMatching_edgeCover G with ⟨M, hM, _hmax, hcover⟩
  letI : DecidableRel M.Adj := Classical.decRel _
  letI : Fintype M.verts := M.verts.toFinite.fintype
  let T : Finset (Fin n) := M.verts.toFinset
  refine ⟨T, ?_, ?_⟩
  · have hedge_lt : M.coe.edgeFinset.card < Fintype.card (F j).V := by
      by_contra hnot
      have hedge_ge : Fintype.card (F j).V ≤ M.coe.edgeFinset.card := by
        omega
      have hH_to_matching :
          EmbedsAsSubgraph (F j).graph (matchingGraph (Fintype.card (F j).V)) :=
        embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
          (F j).graph hmatching.1
      have hmatching_to_G :
          EmbedsAsSubgraph (matchingGraph (Fintype.card (F j).V)) G :=
        matching_embedding_of_edgeFinset_card_ge M hM hedge_ge
      exact hfree j (hH_to_matching.trans hmatching_to_G)
    have hT :
        T.card = 2 * M.coe.edgeFinset.card := by
      simpa [T] using
        matching_verts_toFinset_card_eq_two_mul_edgeFinset_card M hM
    have hedge_le : M.coe.edgeFinset.card ≤ Fintype.card (F j).V - 1 := by
      omega
    calc
      T.card = 2 * M.coe.edgeFinset.card := hT
      _ ≤ 2 * (Fintype.card (F j).V - 1) :=
        Nat.mul_le_mul_left 2 hedge_le
  · intro x y hxy
    simpa [T] using hcover hxy
end
namespace Arexychen
noncomputable section
namespace Erdos180




end Erdos180

end
end Arexychen
