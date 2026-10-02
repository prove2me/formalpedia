-- Prove2me | solution 1 for Arexychen.Erdos180.edgeCount_le_of_star_free_of_matching_free
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:33:26.584669+00:00
-- url     : https://prove2.me/submissions/137f362b-0872-49e2-bac2-d9ec2a6ee541

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic
import Theorems.Thm_Arexychen_Erdos180_edgeCount_le_card_mul_degree_bound_of_edges_meet_finset
import Theorems.Thm_Arexychen_Erdos180_exists_maximalMatching_edgeCover
import Theorems.Thm_Arexychen_Erdos180_matching_embedding_of_edgeFinset_card_ge

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

namespace Arexychen




open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

private theorem starFin_embedding_of_degree_ge
    {V : Type u} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)]
    {a : ℕ} (hdeg : a ≤ G.degree v) :
    EmbedsAsSubgraph (starGraph (0 : Fin (a + 1))) G := by
  classical
  let c : Fin (a + 1) := 0
  have hcard : Fintype.card (Fin a) ≤ Fintype.card (G.neighborSet v) := by
    simpa only [Fintype.card_fin, G.card_neighborSet_eq_degree] using hdeg
  rcases Function.Embedding.nonempty_of_card_le hcard with
    ⟨leaf : Fin a ↪ G.neighborSet v⟩
  let leafIndex : {x : Fin (a + 1) // x ≠ c} → Fin a :=
    (finSuccAboveEquiv c).symm
  let f : Fin (a + 1) → V := fun x =>
    if hx : x = c then v else leaf (leafIndex ⟨x, hx⟩)
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = c
    · by_cases hy : y = c
      · exact hx.trans hy.symm
      · exfalso
        have hv_leaf : v = (leaf (leafIndex ⟨y, hy⟩) : V) := by
          simpa [f, hx, hy] using hxy
        exact (leaf (leafIndex ⟨y, hy⟩)).property.ne hv_leaf
    · by_cases hy : y = c
      · exfalso
        have hleaf_v : (leaf (leafIndex ⟨x, hx⟩) : V) = v := by
          simpa [f, hx, hy] using hxy
        exact (leaf (leafIndex ⟨x, hx⟩)).property.ne hleaf_v.symm
      · have hidx : leafIndex ⟨x, hx⟩ = leafIndex ⟨y, hy⟩ := by
          have hleaf :
              (leaf (leafIndex ⟨x, hx⟩) : V) =
                (leaf (leafIndex ⟨y, hy⟩) : V) := by
            simpa [f, hx, hy] using hxy
          exact leaf.injective (Subtype.ext hleaf)
        have hsub :
            (⟨x, hx⟩ : {x : Fin (a + 1) // x ≠ c}) = ⟨y, hy⟩ := by
          exact (Equiv.injective (finSuccAboveEquiv c).symm) hidx
        exact congrArg Subtype.val hsub
  · intro x y hxy
    rcases hxy with h | h
    · rcases h with ⟨hx, hy⟩
      have hx' : x = c := by simpa [c] using hx
      have hy' : y ≠ c := by simpa [c] using hy
      have hfx : f x = v := by simp [f, hx']
      have hfy : f y = (leaf (leafIndex ⟨y, hy'⟩) : V) := by
        simp [f, hy']
      rw [hfx, hfy]
      exact (leaf (leafIndex ⟨y, hy'⟩)).property
    · rcases h with ⟨hy, hx⟩
      have hy' : y = c := by simpa [c] using hy
      have hx' : x ≠ c := by simpa [c] using hx
      have hfx : f x = (leaf (leafIndex ⟨x, hx'⟩) : V) := by
        simp [f, hx']
      have hfy : f y = v := by simp [f, hy']
      rw [hfx, hfy]
      exact ((leaf (leafIndex ⟨x, hx'⟩)).property).symm

private theorem maxDegree_le_pred_of_star_free
    {n a : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hstar : IsHFree (starGraph (0 : Fin (a + 1))) G) :
    G.maxDegree ≤ a - 1 := by
  classical
  refine G.maxDegree_le_of_forall_degree_le (a - 1) ?_
  intro v
  by_contra hnot
  have hdeg : a ≤ G.degree v := by
    omega
  exact hstar (starFin_embedding_of_degree_ge G v hdeg)

private theorem exists_edgeCover_card_le_two_mul_pred_of_matching_free
    {n b : ℕ} (G : SimpleGraph (Fin n))
    (hmatch : IsHFree (matchingGraph b) G) :
    ∃ T : Finset (Fin n),
      T.card ≤ 2 * (b - 1) ∧
        ∀ ⦃x y : Fin n⦄, G.Adj x y → x ∈ T ∨ y ∈ T := by
  classical
  rcases exists_maximalMatching_edgeCover G with ⟨M, hM, _hmax, hcover⟩
  letI : DecidableRel M.Adj := Classical.decRel _
  letI : Fintype M.verts := M.verts.toFinite.fintype
  let T : Finset (Fin n) := M.verts.toFinset
  refine ⟨T, ?_, ?_⟩
  · have hedge_lt : M.coe.edgeFinset.card < b := by
      by_contra hnot
      have hedge_ge : b ≤ M.coe.edgeFinset.card := by
        omega
      exact hmatch
        (matching_embedding_of_edgeFinset_card_ge M hM hedge_ge)
    have hT :
        T.card = 2 * M.coe.edgeFinset.card := by
      simpa [T] using
        matching_verts_toFinset_card_eq_two_mul_edgeFinset_card M hM
    have hedge_le : M.coe.edgeFinset.card ≤ b - 1 := by
      omega
    calc
      T.card = 2 * M.coe.edgeFinset.card := hT
      _ ≤ 2 * (b - 1) := Nat.mul_le_mul_left 2 hedge_le
  · intro x y hxy
    simpa [T] using hcover hxy

-- `[DecidableRel G.Adj]` is unused in the statement but required by the
-- proof (`maxDegree`), hence the linter override.
end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
set_option linter.unusedDecidableInType false in
theorem solution
    {n a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hstar : IsHFree (starGraph (0 : Fin (a + 1))) G)
    (hmatch : IsHFree (matchingGraph b) G) :
    edgeCount G ≤ 2 * (a - 1) * (b - 1) := by
  classical
  have _ha : 1 ≤ a - 1 := by omega
  have _hb : 1 ≤ b - 1 := by omega
  have hmax : G.maxDegree ≤ a - 1 :=
    maxDegree_le_pred_of_star_free G hstar
  rcases exists_edgeCover_card_le_two_mul_pred_of_matching_free G hmatch with
    ⟨T, hTcard, hcover⟩
  have hbound :
      edgeCount G ≤ 2 * (b - 1) * (a - 1) :=
    edgeCount_le_two_mul_pred_mul_pred_of_maxDegree_and_edgeCover
      G a b T hmax hTcard hcover
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbound
end
namespace Arexychen
noncomputable section
namespace Erdos180




end Erdos180

end
end Arexychen
