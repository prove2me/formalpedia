-- Prove2me | solution 1 for VertexSplitting.exists_singleSplit_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:56:46.377327+00:00
-- url     : https://prove2.me/submissions/bb5da1a5-e80d-4fbf-ab51-2308f3678b8b

-- Sol generated from Bridges/VertexSplitting.lean
import Mathlib
import Definitions.Def_Bridges_VertexSplitting
import Theorems.Thm_VertexSplitting_isSplit_singleSplit
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
theorem solution{G : SimpleGraph V} {H : SimpleGraph W} {f : W → V}
    (h : IsSplit G H f) (w₀ w₁ : W) (hne : w₀ ≠ w₁) (heq : f w₁ = f w₀) :
    ∃ (A B : Set V) (g : W → V ⊕ Unit),
      IsSplit G (singleSplit G (f w₀) A B) (splitMap (f w₀)) ∧
      IsSplit (singleSplit G (f w₀) A B) H g ∧
      f = splitMap (f w₀) ∘ g ∧
      (∀ x, g x = Sum.inr () ↔ x = w₀) ∧
      (IsProjExclusive H f → ∀ u ∈ A, u ∉ B) ∧
      (IsProjExclusive H f → IsProjExclusive H g) := by
  classical
  set v := f w₀ with hv
  set A : Set V := {u | ∃ w z, f w = v ∧ w ≠ w₀ ∧ H.Adj w z ∧ f z = u} with hA
  set B : Set V := {u | ∃ z, H.Adj w₀ z ∧ f z = u} with hB
  set g : W → V ⊕ Unit := fun x => if x = w₀ then Sum.inr () else Sum.inl (f x) with hg
  have hg0 : g w₀ = Sum.inr () := by simp [hg]
  have hg1 : ∀ x, x ≠ w₀ → g x = Sum.inl (f x) := fun x hx => by simp [hg, hx]
  have hmemA : ∀ u, u ∈ A ↔ ∃ w z, f w = v ∧ w ≠ w₀ ∧ H.Adj w z ∧ f z = u := fun _ => Iff.rfl
  have hmemB : ∀ u, u ∈ B ↔ ∃ z, H.Adj w₀ z ∧ f z = u := fun _ => Iff.rfl
  refine ⟨A, B, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the one-step split of `v` is a legitimate split of `G`
    refine isSplit_singleSplit G v A B ?_ ?_ ?_
    · rintro u ⟨w, z, hw, -, hadj, hz⟩
      have := h.adj_proj _ _ hadj
      rwa [hw, hz] at this
    · rintro u ⟨z, hadj, hz⟩
      have := h.adj_proj _ _ hadj
      rwa [hz] at this
    · intro u hu
      obtain ⟨p, q, hp, hq, hpq⟩ := h.cover v u hu
      by_cases hpw : p = w₀
      · exact Or.inr ((hmemB u).mpr ⟨q, hpw ▸ hpq, hq⟩)
      · exact Or.inl ((hmemA u).mpr ⟨p, q, hp, hpw, hpq, hq⟩)
  · -- `H` is a splitting of the one-step split
    constructor
    · rintro (u | u)
      · by_cases hu : u = v
        · exact ⟨w₁, by rw [hg1 w₁ (Ne.symm hne), heq, hu]⟩
        · obtain ⟨x, hx⟩ := h.surj u
          have hxw : x ≠ w₀ := fun hc => hu (by rw [← hx, hc])
          exact ⟨x, by rw [hg1 x hxw, hx]⟩
      · exact ⟨w₀, by rw [hg0]⟩
    · intro x y hxy hadj
      by_cases hx : x = w₀ <;> by_cases hy : y = w₀
      · subst hx; subst hy; exact H.irrefl hadj
      · rw [hx, hg0, hg1 y hy] at hxy; exact absurd hxy (by simp)
      · rw [hy, hg0, hg1 x hx] at hxy; exact absurd hxy (by simp)
      · rw [hg1 x hx, hg1 y hy] at hxy
        exact h.fiber_indep x y (by simpa using hxy) hadj
    · intro x y hadj
      by_cases hx : x = w₀ <;> by_cases hy : y = w₀
      · exact absurd (hx.trans hy.symm) (H.ne_of_adj hadj)
      · rw [hx, hg0, hg1 y hy]
        exact (hmemB (f y)).mpr ⟨y, hx ▸ hadj, rfl⟩
      · rw [hy, hg0, hg1 x hx]
        exact (hmemB (f x)).mpr ⟨x, hy ▸ hadj.symm, rfl⟩
      · rw [hg1 x hx, hg1 y hy]
        exact ⟨h.adj_proj _ _ hadj, fun hfx => (hmemA (f y)).mpr ⟨x, y, hfx, hx, hadj, rfl⟩,
          fun hfy => (hmemA (f x)).mpr ⟨y, x, hfy, hy, hadj.symm, rfl⟩⟩
    · rintro (a | a) (b | b) hab
      · simp only [singleSplit, splitAdj] at hab
        obtain ⟨hGab, hav, hbv⟩ := hab
        by_cases ha : a = v
        · obtain ⟨w, z, hw, hwne, hwz, hz⟩ := (hmemA b).mp (hav ha)
          have hzw : z ≠ w₀ := by
            intro hc
            rw [hc] at hz
            exact G.irrefl (ha ▸ hz ▸ hGab)
          exact ⟨w, z, by rw [hg1 w hwne, hw, ha], by rw [hg1 z hzw, hz], hwz⟩
        · by_cases hb : b = v
          · obtain ⟨w, z, hw, hwne, hwz, hz⟩ := (hmemA a).mp (hbv hb)
            have hzw : z ≠ w₀ := by
              intro hc
              rw [hc] at hz
              exact ha hz.symm
            exact ⟨z, w, by rw [hg1 z hzw, hz], by rw [hg1 w hwne, hw, hb], hwz.symm⟩
          · obtain ⟨x, y, hx, hy, hxy⟩ := h.cover a b hGab
            have hxw : x ≠ w₀ := fun hc => ha (by rw [← hx, hc])
            have hyw : y ≠ w₀ := fun hc => hb (by rw [← hy, hc])
            exact ⟨x, y, by rw [hg1 x hxw, hx], by rw [hg1 y hyw, hy], hxy⟩
      · simp only [singleSplit, splitAdj] at hab
        obtain ⟨z, hz, hzf⟩ := (hmemB a).mp hab
        have hzw : z ≠ w₀ := (H.ne_of_adj hz).symm
        exact ⟨z, w₀, by rw [hg1 z hzw, hzf], by rw [hg0], hz.symm⟩
      · simp only [singleSplit, splitAdj] at hab
        obtain ⟨z, hz, hzf⟩ := (hmemB b).mp hab
        have hzw : z ≠ w₀ := (H.ne_of_adj hz).symm
        exact ⟨w₀, z, by rw [hg0], by rw [hg1 z hzw, hzf], hz⟩
      · simp only [singleSplit, splitAdj] at hab
  · -- the factorization of `f`
    funext x
    by_cases hx : x = w₀
    · rw [Function.comp_apply, hx, hg0]
      rfl
    · rw [Function.comp_apply, hg1 x hx]
      rfl
  · intro x
    constructor
    · intro hx
      by_contra hc
      rw [hg1 x hc] at hx
      exact absurd hx (by simp)
    · intro hx
      rw [hx, hg0]
  · rintro hpe u hu hu'
    obtain ⟨w, z, hw, hwne, hwz, hz⟩ := (hmemA u).mp hu
    obtain ⟨z', hz', hzf'⟩ := (hmemB u).mp hu'
    exact hpe w w₀ z z' hw hwne hwz hz' (hz.trans hzf'.symm)
  · intro hpe x y z z' hxy hne' hxz hyz' hzz'
    by_cases hx : x = w₀ <;> by_cases hy : y = w₀
    · exact hne' (hx.trans hy.symm)
    · rw [hx, hg0, hg1 y hy] at hxy; exact absurd hxy (by simp)
    · rw [hy, hg0, hg1 x hx] at hxy; exact absurd hxy (by simp)
    · rw [hg1 x hx, hg1 y hy] at hxy
      have hfxy : f x = f y := by simpa using hxy
      have hne'' : f z ≠ f z' := hpe x y z z' hfxy hne' hxz hyz'
      by_cases hz : z = w₀ <;> by_cases hz2 : z' = w₀
      · exact hne'' (by rw [hz, hz2])
      · rw [hz, hg0, hg1 z' hz2] at hzz'; exact absurd hzz' (by simp)
      · rw [hz2, hg0, hg1 z hz] at hzz'; exact absurd hzz' (by simp)
      · rw [hg1 z hz, hg1 z' hz2] at hzz'
        exact hne'' (by simpa using hzz')
