-- Prove2me | solution 1 for TriangularForest.four_mul_lt_choose_two_add_six
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:50:30.435908+00:00
-- url     : https://prove2.me/submissions/5e1f4789-308b-4fbb-8102-3dc385e30a34

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
theorem solution{n : ℕ} (hn : 8 ≤ n) : 4 * n < n.choose 2 + 6 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 8 with hm | hm
    · have hm7 : m = 7 := by omega
      subst hm7
      decide
    · have hstep : (m + 1).choose 2 = m.choose 2 + m := by
        rw [Nat.choose_succ_succ m 1]
        simp [Nat.choose_one_right, Nat.add_comm]
      have := ih (by omega)
      omega
