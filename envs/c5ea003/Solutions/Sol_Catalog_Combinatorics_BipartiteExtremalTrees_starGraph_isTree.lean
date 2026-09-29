-- Prove2me | solution 1 for Catalog.Combinatorics.BipartiteExtremalTrees.starGraph_isTree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:05:42.707198+00:00
-- url     : https://prove2.me/submissions/b424a5db-4267-4b7e-bce2-0e3fe5157e9f

-- Sol generated from Combinatorics/BipartiteExtremalTreesErdosSos.lean
import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees
import Definitions.Def_Combinatorics_BipartiteExtremalTreesFixedParts
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A linear Erdős–Sós type upper bound for *every* tree, bipartite and not

This file settles, up to a factor of two in the slope, Conjecture 2 of the research thread
started in `Catalog/Combinatorics/BipartiteExtremalTrees.lean`: the bipartite extremal number of
a tree is linear in the order of the host, with a slope depending only on the tree.

The engine is the classical *greedy embedding lemma*, formalised here in full:

* `tree_isContained_of_forall_le_degree`: **every** graph whose minimum degree is at least the
  number of edges of a tree `T` contains a copy of `T`.  The proof is an induction on the order
  of `T` in which a leaf is removed (`SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`),
  the smaller tree is embedded by the inductive hypothesis, and the leaf is placed on a neighbour
  of the image of its parent that has not been used yet — such a neighbour exists precisely
  because the degree bound exceeds the number of already embedded vertices.

Its consequences, obtained by deleting a vertex of small degree and inducting on the order of the
host (so that a `T`-free graph is exhibited as `(k-1)`-degenerate):

* `exists_degree_le_of_isTree_free`: a `T`-free graph has a vertex of degree at most `k - 1`.
* `card_edgeFinset_le_of_isTree_free`: a `T`-free graph on `N` vertices has at most `(k-1)·N`
  edges, `k` being the number of edges of the tree `T`.
* `exBip_le_of_isTree`, `exBipParts_le_of_isTree`, `extremalNumber_le_of_isTree`: the same bound
  for the three extremal functions, i.e. **a linear bipartite Erdős–Sós bound for all trees**.
* `two_mul_exBip_le_of_isTree`: the bound in the normalisation of the Erdős–Sós conjecture,
  `2·exBip n T ≤ 2(k-1)·n`, so the conjectural slope `k-1` is missed by at most a factor of two.

Two families are then fed into the general theorem.

* `starGraph_isTree` and `star_greedy_bound_factor_two_sharp`: for stars the greedy bound is
  *exactly* a factor two off the truth `exBip n K_{1,k+1} = k⌊n/2⌋`, so no strengthening of the
  degeneracy argument alone can beat the factor two in general.
* `pathGraph_isAcyclic`, `pathGraph_isTree` (the acyclicity proof — a bridge/side-invariant
  argument — appears to be missing from Mathlib) and `exBip_pathGraph_bounds`:
  `(⌊p/2⌋-1)(n-⌊p/2⌋+1) ≤ exBip n P_p ≤ (p-2)·n`, sandwiching the bipartite extremal number of
  every path between two explicit linear functions of `n`.  For `p = 4` the two sides are
  `n - 1` and `2n`, and the exact answer `n - 1` (`exBip_pathGraph_four`) sits at the lower end.
-/

open Catalog.Combinatorics.BipartiteExtremalTrees

open Finset Fintype SimpleGraph

universe u v

/-! ### The greedy embedding lemma -/




/-! ### The linear upper bound -/







/-! ### Stars: the greedy bound is off by exactly a factor of two -/

/-- A vertex with no incident edges is unreachable from any other vertex. -/
theorem not_reachable_of_isolated {V : Type*} {H : SimpleGraph V} {x y : V}
    (hiso : ∀ z, ¬ H.Adj z y) (hxy : x ≠ y) : ¬ H.Reachable x y := by
  rintro ⟨p⟩
  have key : ∀ {a b : V} (_ : H.Walk a b), a ≠ y → b ≠ y := by
    intro a b q
    induction q with
    | nil => exact id
    | cons h _ ih =>
        intro _
        exact ih (fun hz => hiso _ (hz ▸ h))
  exact key p hxy rfl




/-! ### Paths: a two-sided linear estimate -/







open Catalog.Combinatorics.BipartiteExtremalTrees in
theorem solution(k : ℕ) : (starGraph k).IsTree := by
  constructor
  · rw [connected_iff]
    refine ⟨?_, ⟨Sum.inl ()⟩⟩
    have hstar : ∀ c : Unit ⊕ Fin k, (starGraph k).Reachable (Sum.inl ()) c := by
      rintro (⟨⟩ | c)
      · rfl
      · exact SimpleGraph.Adj.reachable (by simp [starGraph])
    exact fun a b => (hstar a).symm.trans (hstar b)
  · rw [isAcyclic_iff_forall_adj_isBridge]
    intro a b hab
    rw [isBridge_iff]
    refine ⟨hab, ?_⟩
    rcases a with ⟨⟩ | i <;> rcases b with ⟨⟩ | j
    · simp [starGraph] at hab
    · -- deleting the edge isolates the leaf `inr j`
      refine not_reachable_of_isolated ?_ (by simp)
      rintro (⟨⟩ | z) hz
      · exact hz.2 (by rw [fromEdgeSet_adj]; exact ⟨by simp, hz.1.ne⟩)
      · simp [starGraph] at hz
    · intro hreach
      refine not_reachable_of_isolated (y := Sum.inr i) ?_ (by simp) hreach.symm
      rintro (⟨⟩ | z) hz
      · exact hz.2 (by rw [fromEdgeSet_adj]; exact ⟨by simp [Sym2.eq_swap], hz.1.ne⟩)
      · simp [starGraph] at hz
    · simp [starGraph] at hab
