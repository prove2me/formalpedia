-- Prove2me | solution 1 for VertexSplitting.isSplit_singleSplit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:55:16.931179+00:00
-- url     : https://prove2.me/submissions/54f076b2-5a93-4432-80a5-4facb300f724

-- Sol generated from Bridges/VertexSplitting.lean
import Mathlib
import Definitions.Def_Bridges_VertexSplitting
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vertex Splitting: a formal model, and universal splitting constructions

Motivated by the paper *Hardness of Vertex Splitting: Cographs, Chordal Graphs, and Beyond*,
this file develops a formal, type-theoretic model of the **vertex splitting** operation on
simple graphs and proves structural results about it.

## The model

A single *vertex split* replaces a vertex `v` of a graph `G` by two nonadjacent vertices whose
neighbourhoods together cover `N(v)`.  Iterating splits, a graph `H` on a vertex type `W` is
obtainable from `G` on `V` exactly when there is a *splitting map* `f : W → V` such that

* `f` is surjective (no vertex disappears),
* every fibre `f⁻¹(u)` is an independent set of `H` (the copies of a vertex are nonadjacent),
* `f` maps edges of `H` to edges of `G` (no new adjacencies appear), and
* every edge of `G` is covered by an edge of `H` (the copies' neighbourhoods cover `N(u)`).

This is captured by `VertexSplitting.IsSplit`.  We justify the model by exhibiting the
one-step split explicitly (`VertexSplitting.singleSplit`, `VertexSplitting.isSplit_singleSplit`)
and showing that the relation is reflexive and transitive.

## Main results

* `VertexSplitting.IsSplit.comp`: splitting maps compose (splits can be iterated).
* `VertexSplitting.IsSplit.card_le`: splitting never decreases the number of vertices.
* `VertexSplitting.IsSplit.card_edgeFinset_le`: splitting never decreases the number of edges.
* `VertexSplitting.IsSplit.adj_iff_of_injective`: a splitting map that adds no vertex is an
  isomorphism, i.e. zero splits change nothing.
* `VertexSplitting.isSplit_singleSplit`: the explicit one-step split is a splitting map.
* `VertexSplitting.isSplit_matchingGraph`: splitting each vertex `v` into `deg v` copies turns
  any graph without isolated vertices into a perfect matching, using `2|E| - |V|` splits, and
  this splitting is *exclusive*.
* `VertexSplitting.isCograph_matchingGraph`, `isChordal_matchingGraph`,
  `hasUnitIntervalRep_matchingGraph`: the resulting graph is a cograph (`P₄`-free), chordal,
  and a unit interval graph.
* `VertexSplitting.isPtFree_matchingGraph`: the result is moreover `P_t`-free for every
  `t ≥ 3`, covering the whole `P_t`-free hierarchy considered in the paper.
* `VertexSplitting.two_mul_card_edgeFinset_le_of_split_matching`: `2|E| - |V|` splits are also
  *necessary* whenever the target has maximum degree at most one, so the construction is exact.
* `VertexSplitting.card_lt_of_split_cograph`, `card_lt_of_split_chordal`: a graph that is not
  already a cograph (resp. chordal) needs at least one split, since a splitting map that adds
  no vertex is an isomorphism.
* `VertexSplitting.exists_split_cograph_chordal_unitInterval`: the resulting universal upper
  bound `2|E| - |V|` on the splitting number for all these target classes.
* `VertexSplitting.exists_singleSplit_factor` and `VertexSplitting.SplitChain.of_isSplit`:
  every splitting map between finite graphs factors as a chain of explicit *single* splits,
  and the chain can always be taken **shallow** (a newly created vertex is never split again);
  if the splitting is exclusive (`IsProjExclusive`) then every single split in the chain is
  exclusive as well.
* `VertexSplitting.splitChain_matchingGraph`: in particular the universal `2|E| - |V|`
  splitting is realized by a shallow, exclusive chain of single splits.
* `VertexSplitting.not_hasInducedClaw_of_unitIntervalRep`: unit interval graphs are claw-free,
  whence `VertexSplitting.card_lt_of_split_unitInterval`: a graph with an induced claw needs
  at least one split to become a unit interval graph (`starK13` is an explicit witness).
-/


open VertexSplitting

open SimpleGraph Finset

variable {V W X : Type*}

/-! ## The splitting relation -/





/-! ## Basic invariants -/




/-! ## The one-step split -/







/-! ## Target graph classes -/








/-! ## `P_t`-freeness -/





/-! ## Transfer of forbidden structures along injective splitting maps -/





/-! ## The universal splitting: turning any graph into a perfect matching -/

variable (G : SimpleGraph V)


variable {G}








/-! ## Optimality of the universal splitting among matching targets -/




/-! ## The universal upper bound on splitting numbers -/


/-! ## Factorization of a splitting into single, shallow splits

The paper distinguishes general splittings from *shallow* ones (no newly created vertex is
split again) and from *exclusive* ones (the copies of a split vertex get disjoint
neighbourhoods).  In this section we show that the abstract model `IsSplit` loses nothing:
every splitting map factors as a chain of explicit single splits (`singleSplit`), and this
chain can always be chosen **shallow**; moreover if the splitting is exclusive (in the
projected sense below) then every single split in the chain is exclusive as well. -/




universe u






/-! ## Unit interval graphs are claw-free -/





/-! ## Sanity checks: the forbidden structures are really present in the standard examples -/













open VertexSplitting in
theorem solution(G : SimpleGraph V) (v : V) (A B : Set V)
    (hA : ∀ x ∈ A, G.Adj v x) (hB : ∀ x ∈ B, G.Adj v x)
    (hAB : ∀ x, G.Adj v x → x ∈ A ∨ x ∈ B) :
    IsSplit G (singleSplit G v A B) (splitMap v) where
  surj := fun u => ⟨Sum.inl u, rfl⟩
  fiber_indep := by
    rintro (x | x) (y | y) hxy hadj <;>
      simp only [splitMap, Sum.elim_inl, Sum.elim_inr, id_eq] at hxy <;>
      simp only [singleSplit, splitAdj] at hadj
    · subst hxy; exact G.irrefl hadj.1
    · have := hB x hadj; rw [hxy] at this; exact G.irrefl this
    · have := hB y hadj; rw [← hxy] at this; exact G.irrefl this
  adj_proj := by
    rintro (x | x) (y | y) hadj <;>
      simp only [singleSplit, splitAdj] at hadj <;>
      simp only [splitMap, Sum.elim_inl, Sum.elim_inr, id_eq]
    · exact hadj.1
    · exact (hB x hadj).symm
    · exact hB y hadj
  cover := by
    intro u w huw
    rcases eq_or_ne u v with rfl | hu
    · rcases hAB w huw with hw | hw
      · refine ⟨Sum.inl u, Sum.inl w, rfl, rfl, ?_⟩
        refine ⟨huw, fun _ => hw, fun h => ?_⟩
        exact absurd (h ▸ huw) (G.irrefl)
      · exact ⟨Sum.inr (), Sum.inl w, rfl, rfl, hw⟩
    · rcases eq_or_ne w v with rfl | hw
      · rcases hAB u huw.symm with hu' | hu'
        · refine ⟨Sum.inl u, Sum.inl w, rfl, rfl, ?_⟩
          exact ⟨huw, fun h => absurd (h ▸ huw) (G.irrefl), fun _ => hu'⟩
        · exact ⟨Sum.inl u, Sum.inr (), rfl, rfl, hu'⟩
      · exact ⟨Sum.inl u, Sum.inl w, rfl, rfl,
          ⟨huw, fun h => absurd h hu, fun h => absurd h hw⟩⟩
