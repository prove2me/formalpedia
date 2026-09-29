-- Prove2me | solution 1 for Catalog.Novelty.CycleFamilies.shatter_containsCycle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:58:56.210987+00:00
-- url     : https://prove2.me/submissions/41ea21fa-1473-4cc6-8953-f565c1209b4f

-- Sol generated from Novelty/Binary.lean
import Mathlib
import Definitions.Def_Novelty_Binary
import Definitions.Def_Novelty_General
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cycle-containing families over a binary alphabet (`b = 2`)

For the binary alphabet `Fin 2` the bipartite graph of a pair has only four
possible edges, and its **only** possible cycle is the 4-cycle of the complete
bipartite graph `K₂,₂`.  Hence a pair `(u, v)` is cycle-containing iff all four
"patterns" `(s, t) ∈ Fin 2 × Fin 2` occur among the coordinates — the classical
notion of two binary vectors being *qualitatively independent*.

We package this combinatorial criterion as `Shatter`, connect it to the genuine
graph-theoretic predicate `ContainsCycle` from `CycleFamilies.General` via
`shatter_containsCycle`, and use it to:

* `shatter_k_ge_four`      : a shattering pair forces `4 ≤ k` (sharp threshold);
* `shatter_snoc`           : shattering is preserved by extending vectors, so the
                              extremal function is monotone in `k`;
* `exists_cyclicFamily_card_three` : an explicit **genuinely cycle-containing**
                              family of three vectors at `k = 4`, matching the
                              exhaustively-computed maximum (see
                              `ComputationalEvidence.md`).

-- !-- Lab Notes -- !--
Hypothesis  : Over `Fin 2` the graph cycle condition is equivalent to "all four
              patterns appear" (qualitative independence), and the maximum cyclic
              family has sizes `1,1,3,4,10,15,…` for `k = 2,3,4,5,6,7`.
Experiment  : Brute-force max-clique enumeration produced the sequence above.
              Formally, `Shatter` says the coordinate map `i ↦ (u i, v i)` is onto
              `Fin 2 × Fin 2`; surjectivity onto a 4-element type forces `k ≥ 4`.
              The explicit triple `{0011, 0101, 0110}` was verified to be pairwise
              shattering by `decide`, then promoted to genuine `ContainsCycle` via
              the constructed 4-cycle walk `shatter_containsCycle`.
Analysis    : Lower bound `3` at `k = 4` is exact (brute force gives `3`); proving
              the matching *upper* bound `≤ 3` for `k = 4`, and the general formula
              `N₂(k)`, are open (recorded in FUTURE_DIRECTIONS).  The threshold and
              monotonicity are the clean, fully-formal facts.
Critique    : `decide` is used only for the finite verification of a *single*
              witness family, never as the proof of a structural theorem.  The
              structural theorems use `Fintype.card_le_of_surjective`, an explicit
              walk construction, and `Fin.snoc` case analysis.
Synthesis   : The binary world realises the general girth bound sharply and
              exhibits the first nontrivial cyclic families.
-/

open SimpleGraph Finset

open Catalog.Novelty.CycleFamilies

variable {k : ℕ}



/-- A coordinate realising pattern `(a, c)` gives an edge `inl a — inr c`. -/
theorem adj_of_pat (u v : Fin k → Fin 2) (a c : Fin 2) (i : Fin k)
    (h1 : u i = a) (h2 : v i = c) :
    (pairGraph u v).Adj (Sum.inl a) (Sum.inr c) := by
  subst h1 h2
  rw [pairGraph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨i, rfl⟩, by simp⟩







open Catalog.Novelty.CycleFamilies in
theorem solution(u v : Fin k → Fin 2) (h : Shatter u v) :
    ContainsCycle u v := by
  obtain ⟨i00, e00u, e00v⟩ := h 0 0
  obtain ⟨i01, e01u, e01v⟩ := h 0 1
  obtain ⟨i10, e10u, e10v⟩ := h 1 0
  obtain ⟨i11, e11u, e11v⟩ := h 1 1
  have a00 := adj_of_pat u v 0 0 i00 e00u e00v
  have a01 := adj_of_pat u v 0 1 i01 e01u e01v
  have a10 := adj_of_pat u v 1 0 i10 e10u e10v
  have a11 := adj_of_pat u v 1 1 i11 e11u e11v
  intro hac
  refine hac (Walk.cons a00 (.cons a10.symm (.cons a11 (.cons a01.symm .nil)))) ?_
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
    decide
  · simp
  · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    decide
