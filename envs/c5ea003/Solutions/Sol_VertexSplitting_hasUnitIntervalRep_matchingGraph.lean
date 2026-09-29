-- Prove2me | solution 1 for VertexSplitting.hasUnitIntervalRep_matchingGraph
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:56:46.919987+00:00
-- url     : https://prove2.me/submissions/9e34b920-6b2b-41b0-a55b-f6e26fb776c6

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
theorem solution[Fintype V] [LinearOrder V] :
    HasUnitIntervalRep (matchingGraph G) := by
  classical
  have key : ∀ a b : ℕ, a < b → ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      1 < |3 * (a : ℝ) + s - (3 * (b : ℝ) + t)| := by
    intro a b hab s t hs hs1 ht ht1
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
    rw [abs_sub_comm]
    refine lt_of_lt_of_le ?_ (le_abs_self _)
    linarith
  set ι : Sym2 V → ℕ := fun s => ((Fintype.equivFin (Sym2 V)) s : ℕ) with hι
  have hιinj : Function.Injective ι := by
    intro a b hab
    exact (Fintype.equivFin (Sym2 V)).injective (Fin.ext hab)
  refine ⟨fun d => 3 * (ι d.edge : ℝ) + (if d.fst < d.snd then 0 else 1), ?_⟩
  intro d e
  constructor
  · intro hadj
    simp only [matchingGraph] at hadj
    subst hadj
    refine ⟨(Dart.symm_ne d).symm, ?_⟩
    simp only [Dart.edge_symm, Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap]
    rcases lt_or_gt_of_ne d.fst_ne_snd with hlt | hlt
    · rw [if_pos hlt, if_neg (asymm hlt)]
      norm_num
    · rw [if_neg (asymm hlt), if_pos hlt]
      norm_num
  · rintro ⟨hne, hle⟩
    have hedge : d.edge = e.edge := by
      by_contra hE
      have hne' : ι d.edge ≠ ι e.edge := fun hc => hE (hιinj hc)
      have hbound : (1 : ℝ) < |3 * (ι d.edge : ℝ) + (if d.fst < d.snd then 0 else 1) -
          (3 * (ι e.edge : ℝ) + (if e.fst < e.snd then 0 else 1))| := by
        rcases lt_or_gt_of_ne hne' with hlt | hlt
        · exact key _ _ hlt _ _ (by split <;> norm_num) (by split <;> norm_num)
            (by split <;> norm_num) (by split <;> norm_num)
        · rw [abs_sub_comm]
          exact key _ _ hlt _ _ (by split <;> norm_num) (by split <;> norm_num)
            (by split <;> norm_num) (by split <;> norm_num)
      linarith
    rcases (dart_edge_eq_iff d e).mp hedge with h | h
    · exact absurd h hne
    · simp only [matchingGraph]
      rw [h, Dart.symm_symm]
