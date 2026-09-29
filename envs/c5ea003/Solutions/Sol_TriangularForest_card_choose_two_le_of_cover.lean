-- Prove2me | solution 1 for TriangularForest.card_choose_two_le_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:41:48.793999+00:00
-- url     : https://prove2.me/submissions/d14754aa-251a-45d2-b7c5-f8511fb6b764

-- Sol generated from Logic/TriangularForest/Decomposition.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition
import Definitions.Def_Logic_TriangularForest_Defs
import Theorems.Thm_TriangularForest_card_edgeFinset_add_three_le
import Theorems.Thm_TriangularForest_card_edgeFinset_le_sum_of_cover

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
theorem solution{n k : ℕ} (hn : 2 ≤ n)
    (H : Fin k → SimpleGraph (Fin n)) [∀ i, DecidableRel (H i).Adj]
    (hTF : ∀ i, IsTriangularForest (H i))
    (hcov : ∀ x y : Fin n, x ≠ y → ∃ i, (H i).Adj x y) :
    n.choose 2 + 3 * k ≤ k * (2 * n) := by
  classical
  have hcard : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  have hsum : #(⊤ : SimpleGraph (Fin n)).edgeFinset ≤ ∑ i, #(H i).edgeFinset :=
    card_edgeFinset_le_sum_of_cover _ H (fun x y hxy => hcov x y (by simpa using hxy))
  have hbound : ∀ i, #(H i).edgeFinset + 3 ≤ 2 * n := fun i => by
    have := card_edgeFinset_add_three_le (H i) (hTF i) hcard
    simpa using this
  have hsum' : ∑ i, (#(H i).edgeFinset + 3) ≤ ∑ _i : Fin k, (2 * n) :=
    Finset.sum_le_sum fun i _ => hbound i
  rw [Finset.sum_add_distrib] at hsum'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum'
  have htop : #(⊤ : SimpleGraph (Fin n)).edgeFinset = n.choose 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp
  rw [htop] at hsum
  omega
