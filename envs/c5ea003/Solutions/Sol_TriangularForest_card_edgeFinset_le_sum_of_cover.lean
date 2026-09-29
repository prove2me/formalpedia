-- Prove2me | solution 1 for TriangularForest.card_edgeFinset_le_sum_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:39:09.789462+00:00
-- url     : https://prove2.me/submissions/0c8816bb-36ee-411c-bce7-e386a074738e

-- Sol generated from Logic/TriangularForest/Decomposition.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition

/-!
# Edge decompositions into triangular forests

The paper *Edge-decomposition into Two Triangular Forests is NP-complete* studies the decision
problem: given `G`, can `E(G)` be partitioned into two triangular forests?  This file develops
the *extremal* side of that problem, which is what constrains any such decomposition:

* `TriangularForest.DecomposesIntoTwo` — the decision predicate (an edge-disjoint cover by two
  triangular forests);
* `TriangularForest.card_edgeFinset_add_six_le_of_decomposesIntoTwo` — a decomposable graph on
  `n ≥ 2` vertices has at most `4n - 6` edges;
* `TriangularForest.completeGraph_not_decomposesIntoTwo` — consequently `Kₙ` is **not**
  decomposable into two triangular forests for `n ≥ 8`;
* `TriangularForest.completeGraph_decomposesIntoTwo_five` — by contrast `K₅` *is* decomposable,
  an explicit certificate (a triangle with two pendant edges, twice);
* `TriangularForest.card_choose_two_le_of_cover` and
  `TriangularForest.triangularThickness_lower_bound` — the `k`-fold generalisation: covering
  `Kₙ` by `k` triangular forests forces `k ≥ (n-1)/4`, so the "triangular thickness" of `Kₙ`
  grows linearly in `n`.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*}



variable [Fintype V] [DecidableEq V]









variable [Fintype V] [DecidableEq V]















open TriangularForest in
theorem solution{k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Fin k → SimpleGraph V) [∀ i, DecidableRel (H i).Adj]
    (hcov : ∀ x y : V, G.Adj x y → ∃ i, (H i).Adj x y) :
    #G.edgeFinset ≤ ∑ i, #(H i).edgeFinset := by
  classical
  have hsub : G.edgeFinset ⊆ Finset.univ.biUnion fun i => (H i).edgeFinset := by
    intro e he
    induction e with
    | _ x y =>
      simp only [mem_edgeFinset, mem_edgeSet] at he
      obtain ⟨i, hi⟩ := hcov x y he
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, by simpa using hi⟩
  exact le_trans (card_le_card hsub) (Finset.card_biUnion_le)
