-- Prove2me | solution 1 for Catalog.Combinatorics.BipartiteExtremalTrees.pathGraph_isAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:05:42.165278+00:00
-- url     : https://prove2.me/submissions/be37f124-74b1-439b-84ea-2906a626ce31

-- Sol generated from Combinatorics/BipartiteExtremalTreesErdosSos.lean
import Mathlib
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





/-! ### Paths: a two-sided linear estimate -/







open Catalog.Combinatorics.BipartiteExtremalTrees in
theorem solution(n : ℕ) : (pathGraph n).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  rw [isBridge_iff]
  refine ⟨hab, ?_⟩
  intro hreach
  set t : ℕ := min a.val b.val with ht
  set G' := pathGraph n \ fromEdgeSet {s(a, b)} with hG'
  have hstep : ∀ {z y : Fin n}, G'.Adj z y → (z.val ≤ t ↔ y.val ≤ t) := by
    intro z y hzy
    have h1 : (pathGraph n).Adj z y := hzy.1
    have h2 : ¬ (s(z, y) = s(a, b)) := by
      intro hcon
      exact hzy.2 (by rw [fromEdgeSet_adj]; exact ⟨by simp [hcon], h1.ne⟩)
    rw [pathGraph_adj] at h1
    rw [pathGraph_adj] at hab
    have hne : ¬ ((z = a ∧ y = b) ∨ (z = b ∧ y = a)) := by
      intro hcon
      apply h2
      rcases hcon with ⟨h, h'⟩ | ⟨h, h'⟩ <;> subst h <;> subst h' <;> simp [Sym2.eq_swap]
    simp only [Fin.ext_iff, not_or, not_and] at hne
    omega
  have hinv : ∀ {z y : Fin n} (_ : G'.Walk z y), (z.val ≤ t ↔ y.val ≤ t) := by
    intro z y p
    induction p with
    | nil => exact Iff.rfl
    | cons h _ ih => exact (hstep h).trans ih
  obtain ⟨p⟩ := hreach
  have hp := hinv p
  rw [pathGraph_adj] at hab
  omega
