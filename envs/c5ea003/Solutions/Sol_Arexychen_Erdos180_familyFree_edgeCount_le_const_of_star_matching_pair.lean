-- Prove2me | solution 1 for Arexychen.Erdos180.familyFree_edgeCount_le_const_of_star_matching_pair
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:36:28.181566+00:00
-- url     : https://prove2.me/submissions/813e49d2-2180-4032-a72c-5776cc97cbe4

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
import Theorems.Thm_Arexychen_Erdos180_edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
import Theorems.Thm_Arexychen_Erdos180_embeds_of_deleteIsolated_isStar_of_degree_ge_card
import Theorems.Thm_Arexychen_Erdos180_familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v w



/--
The concrete upper bound used in the \(O(1)\) case.  If a graph has maximum
degree at most `a - 1`, and all edges meet a set of at most `2 * (b - 1)`
vertices, then it has at most `2 * (b - 1) * (a - 1)` edges.
-/
private theorem edgeCount_le_two_mul_pred_mul_pred_of_maxDegree_and_edgeCover
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : ℕ) (T : Finset V)
    (hmax : G.maxDegree ≤ a - 1)
    (hTcard : T.card ≤ 2 * (b - 1))
    (hcover : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ T ∨ y ∈ T) :
    edgeCount G ≤ 2 * (b - 1) * (a - 1) := by
  classical
  have hdeg : ∀ v ∈ T, G.degree v ≤ a - 1 := by
    intro v _hv
    exact (G.degree_le_maxDegree v).trans hmax
  exact
    (edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
      G T (a - 1) hdeg hcover).trans
      (Nat.mul_le_mul_right (a - 1) hTcard)















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
Degree-bound extraction from a forbidden star.  If `F i`, after deleting
isolated vertices, is a star, then an `F`-free host graph has maximum degree
bounded by the number of vertices of `F i`.

The proof is the direct pigeonhole embedding argument: if a host vertex had too
many neighbors, send the center of the reduced star to that vertex and inject
all other vertices of `F i` into distinct neighbors.
-/
private theorem familyFree_maxDegree_le_pred_card_of_star
    {ι : Type v} [Finite ι] {F : ι → FiniteSimpleGraph.{u}}
    {i : ι}
    (hstar : (F i).starWithAtLeastTwoEdgesAfterDeletingIsolated)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : FamilyFree F G) :
    G.maxDegree ≤ Fintype.card (F i).V - 1 := by
  classical
  refine G.maxDegree_le_of_forall_degree_le
    (Fintype.card (F i).V - 1) ?_
  intro v
  by_contra hnot
  have hdeg : Fintype.card (F i).V ≤ G.degree v := by
    omega
  exact hfree i
    (embeds_of_deleteIsolated_isStar_of_degree_ge_card
      (F i).graph G v hstar.1 hdeg)







end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
/--
Graph-theoretic bridge for the star/matching obstruction.  The proof extracts
the forbidden star and matching, converts them into a maximum-degree bound and a
bounded matching-number statement, chooses a maximal matching in the host graph,
and applies `edgeCount_le_two_mul_pred_mul_pred_of_maxDegree_and_edgeCover`.
-/
theorem solution
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hpair : FamilyContainsStarMatchingPair F) :
    ∃ C : ℕ, ∀ n (G : SimpleGraph (Fin n)), FamilyFree F G → edgeCount G ≤ C := by
  rcases hpair with ⟨⟨i, hstar⟩, ⟨j, hmatching⟩⟩
  let a : ℕ := Fintype.card (F i).V
  let b : ℕ := Fintype.card (F j).V
  refine ⟨2 * (b - 1) * (a - 1), ?_⟩
  intro n G hfree
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hmax : G.maxDegree ≤ a - 1 := by
    simpa [a] using
      (familyFree_maxDegree_le_pred_card_of_star
        (F := F) (i := i) hstar G hfree)
  rcases
      familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
        (F := F) (j := j) hmatching G hfree with
    ⟨T, hTcard, hcover⟩
  have hTcard' : T.card ≤ 2 * (b - 1) := by
    simpa [b] using hTcard
  exact
    edgeCount_le_two_mul_pred_mul_pred_of_maxDegree_and_edgeCover
      G a b T hmax hTcard' hcover
end
namespace Arexychen
noncomputable section
namespace Erdos180


end Erdos180

end
end Arexychen
