-- Prove2me | solution 1 for VertexSplitting.card_lt_of_split_cograph
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:49:37.970325+00:00
-- url     : https://prove2.me/submissions/564f4f07-c102-4ed3-8445-d7569506e9bc

import Mathlib
import Definitions.Def_Bridges_VertexSplitting

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Bridges/VertexSplitting.lean ====
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

namespace VertexSplitting

open SimpleGraph Finset

variable {V W X : Type*}

/-! ## The splitting relation -/

-- [dropped: platform already declares IsSplit]
-- [dropped: platform already declares IsExclusive]
theorem IsSplit.refl (G : SimpleGraph V) : IsSplit G G id where
  surj := Function.surjective_id
  fiber_indep := by
    intro x y hxy hadj
    simp only [id] at hxy
    subst hxy
    exact G.irrefl hadj
  adj_proj := fun _ _ h => h
  cover := fun u v h => ⟨u, v, rfl, rfl, h⟩

/-- Splitting maps compose: iterating splits is again a splitting. -/
theorem IsSplit.comp {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}
    {f : W → V} {g : X → W} (hf : IsSplit G H f) (hg : IsSplit H K g) :
    IsSplit G K (f ∘ g) where
  surj := hf.surj.comp hg.surj
  fiber_indep := by
    intro x y hxy hadj
    exact hf.fiber_indep _ _ hxy (hg.adj_proj _ _ hadj)
  adj_proj := fun x y h => hf.adj_proj _ _ (hg.adj_proj _ _ h)
  cover := by
    intro u v huv
    obtain ⟨x, y, hx, hy, hxy⟩ := hf.cover u v huv
    obtain ⟨x', y', hx', hy', hxy'⟩ := hg.cover x y hxy
    exact ⟨x', y', by simp [Function.comp, hx', hx], by simp [Function.comp, hy', hy], hxy'⟩

/-! ## Basic invariants -/

theorem IsSplit.card_le [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    {f : W → V} (h : IsSplit G H f) : Fintype.card V ≤ Fintype.card W :=
  Fintype.card_le_of_surjective f h.surj

/-- Splitting never decreases the number of edges. -/
theorem IsSplit.card_edgeFinset_le [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} [DecidableEq V] [DecidableEq W] [Fintype G.edgeSet]
    [Fintype H.edgeSet] {f : W → V} (h : IsSplit G H f) :
    G.edgeFinset.card ≤ H.edgeFinset.card := by
  refine Finset.card_le_card_of_surjOn (Sym2.map f) ?_
  intro e he
  simp only [mem_coe, mem_edgeFinset] at he
  induction e with
  | _ u v =>
    obtain ⟨x, y, hx, hy, hxy⟩ := h.cover u v he
    refine ⟨s(x, y), ?_, ?_⟩
    · simp only [mem_coe, mem_edgeFinset]
      exact hxy
    · simp [hx, hy]

/-- A splitting map that is injective (i.e. that performs no split at all) is an isomorphism
onto `G`: zero splits leave the graph unchanged. -/
theorem IsSplit.adj_iff_of_injective {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V}
    (h : IsSplit G H f) (hf : Function.Injective f) (x y : W) :
    H.Adj x y ↔ G.Adj (f x) (f y) := by
  refine ⟨h.adj_proj x y, fun hadj => ?_⟩
  obtain ⟨x', y', hx', hy', hxy'⟩ := h.cover _ _ hadj
  rwa [hf hx', hf hy'] at hxy'

/-! ## The one-step split -/

/-- Adjacency of the graph obtained from `G` by splitting the vertex `v` into two copies,
the first one (`Sum.inl v`) keeping the neighbours in `A` and the second one (`Sum.inr ()`)
keeping the neighbours in `B`. -/
-- [dropped: platform already declares splitAdj]
-- [dropped: platform already declares singleSplit]
-- [dropped: platform already declares splitMap]
theorem isSplit_singleSplit (G : SimpleGraph V) (v : V) (A B : Set V)
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

/-- A one-step split with disjoint neighbourhoods is exclusive. -/
theorem isExclusive_singleSplit (G : SimpleGraph V) (v : V) (A B : Set V)
    (hdisj : ∀ x, x ∈ A → x ∉ B) :
    IsExclusive (singleSplit G v A B) (splitMap v) := by
  rintro (x | x) (y | y) (z | z) hxy hne hxz hyz <;>
    simp only [splitMap, Sum.elim_inl, Sum.elim_inr, id_eq] at hxy <;>
    simp only [singleSplit, splitAdj] at hxz hyz <;>
    first
      | exact hne (congrArg Sum.inl hxy)
      | exact hne (congrArg Sum.inr (Subsingleton.elim x y))
      | exact hdisj z (hxz.2.1 hxy) hyz
      | exact hdisj z (hyz.2.1 hxy.symm) hxz

/-- A single split adds exactly one vertex. -/
theorem card_singleSplit [Fintype V] :
    Fintype.card (V ⊕ Unit) = Fintype.card V + 1 := by
  simp

/-! ## Target graph classes -/

/-- `G` contains an induced path on four vertices. -/
-- [dropped: platform already declares HasInducedP4]
-- [dropped: platform already declares IsCograph]
-- [dropped: platform already declares HasLongInducedCycle]
-- [dropped: platform already declares IsChordal]
-- [dropped: platform already declares HasUnitIntervalRep]
theorem isCograph_of_deg_le_one {H : SimpleGraph W}
    (h : ∀ x y z, H.Adj x y → H.Adj x z → y = z) : IsCograph H := by
  rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, had⟩
  have hacEq : a = c := h b a c hab.symm hbc
  exact had (hacEq ▸ hcd)

/-- Graphs of maximum degree at most one are chordal. -/
theorem isChordal_of_deg_le_one {H : SimpleGraph W}
    (h : ∀ x y z, H.Adj x y → H.Adj x z → y = z) : IsChordal H := by
  rintro ⟨k, hk, c, hinj, hc⟩
  haveI : NeZero k := ⟨by omega⟩
  have h1 : H.Adj (c 0) (c 1) := (hc 0 1).mpr (Or.inl (by ring))
  have h2 : H.Adj (c 0) (c (-1)) := (hc 0 (-1)).mpr (Or.inr (by ring))
  have heq : (1 : ZMod k) = -1 := hinj (h (c 0) (c 1) (c (-1)) h1 h2)
  have h2z : ((2 : ℕ) : ZMod k) = 0 := by
    push_cast
    linear_combination heq
  rw [ZMod.natCast_eq_zero_iff] at h2z
  have := Nat.le_of_dvd (by norm_num) h2z
  omega

/-! ## `P_t`-freeness -/

/-- `G` contains an induced path on `t` vertices. -/
-- [dropped: platform already declares HasInducedPath]
-- [dropped: platform already declares IsPtFree]
theorem hasInducedP4_of_hasInducedPath_four {G : SimpleGraph V} (h : HasInducedPath G 4) :
    HasInducedP4 G := by
  obtain ⟨p, _, hp⟩ := h
  exact ⟨p 0, p 1, p 2, p 3, (hp 0 1).mpr (by decide), (hp 1 2).mpr (by decide),
    (hp 2 3).mpr (by decide), fun hc => by simpa using (hp 0 2).mp hc,
    fun hc => by simpa using (hp 1 3).mp hc, fun hc => by simpa using (hp 0 3).mp hc⟩

/-- Graphs of maximum degree at most one are `P_t`-free for every `t ≥ 3`. -/
theorem isPtFree_of_deg_le_one {H : SimpleGraph W} (t : ℕ) (ht : 3 ≤ t)
    (h : ∀ x y z, H.Adj x y → H.Adj x z → y = z) : IsPtFree H t := by
  rintro ⟨p, hinj, hp⟩
  have h0 : (0 : ℕ) < t := by omega
  have h1 : (1 : ℕ) < t := by omega
  have h2 : (2 : ℕ) < t := by omega
  set a : Fin t := ⟨0, h0⟩
  set b : Fin t := ⟨1, h1⟩
  set c : Fin t := ⟨2, h2⟩
  have hba : H.Adj (p b) (p a) := (hp b a).mpr (Or.inr rfl)
  have hbc : H.Adj (p b) (p c) := (hp b c).mpr (Or.inl rfl)
  have : a = c := hinj (h (p b) (p a) (p c) hba hbc)
  simp only [a, c, Fin.mk.injEq] at this
  omega

/-! ## Transfer of forbidden structures along injective splitting maps -/

/-- An induced `P₄` of `G` lifts to an induced `P₄` of any zero-split (injective) refinement. -/
theorem hasInducedP4_of_split_injective {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V}
    (h : IsSplit G H f) (hf : Function.Injective f) (hG : HasInducedP4 G) :
    HasInducedP4 H := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, had⟩ := hG
  obtain ⟨a', ha⟩ := h.surj a
  obtain ⟨b', hb⟩ := h.surj b
  obtain ⟨c', hc⟩ := h.surj c
  obtain ⟨d', hd⟩ := h.surj d
  refine ⟨a', b', c', d', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [h.adj_iff_of_injective hf, ha, hb, hc, hd] <;>
    assumption

/-- An induced long cycle of `G` lifts to an induced long cycle of any zero-split (injective)
refinement. -/
theorem hasLongInducedCycle_of_split_injective {G : SimpleGraph V} {H : SimpleGraph W}
    {f : W → V} (h : IsSplit G H f) (hf : Function.Injective f)
    (hG : HasLongInducedCycle G) : HasLongInducedCycle H := by
  obtain ⟨k, hk, c, hinj, hc⟩ := hG
  choose g hg using h.surj
  refine ⟨k, hk, fun i => g (c i), ?_, ?_⟩
  · intro i j hij
    have hfij := congrArg f hij
    rw [hg, hg] at hfij
    exact hinj hfij
  · intro i j
    rw [h.adj_iff_of_injective hf, hg, hg]
    exact hc i j

/-- If `G` is not a cograph but `H` is, then the splitting really had to create a new vertex:
at least one split is necessary. -/
theorem card_lt_of_split_cograph [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    {f : W → V} (h : IsSplit G H f) (hH : IsCograph H) (hG : ¬ IsCograph G) :
    Fintype.card V < Fintype.card W := by
  rcases lt_or_eq_of_le h.card_le with hlt | heq
  · exact hlt
  · exact absurd (hasInducedP4_of_split_injective h
      ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨h.surj, heq.symm⟩).1
      (not_not.mp hG)) hH

/-- If `G` is not chordal but `H` is, then at least one split is necessary. -/
theorem card_lt_of_split_chordal [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    {f : W → V} (h : IsSplit G H f) (hH : IsChordal H) (hG : ¬ IsChordal G) :
    Fintype.card V < Fintype.card W := by
  rcases lt_or_eq_of_le h.card_le with hlt | heq
  · exact hlt
  · exact absurd (hasLongInducedCycle_of_split_injective h
      ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨h.surj, heq.symm⟩).1
      (not_not.mp hG)) hH

/-! ## The universal splitting: turning any graph into a perfect matching -/

variable (G : SimpleGraph V)

-- [dropped: platform already declares matchingGraph]
variable {G}

theorem matchingGraph_deg_le_one (d e e' : G.Dart)
    (h : (matchingGraph G).Adj d e) (h' : (matchingGraph G).Adj d e') : e = e' := by
  simp only [matchingGraph] at h h'
  rw [h, h']

/-- The matching graph on darts is obtained from `G` by vertex splits, as long as `G` has no
isolated vertex (splitting can never delete a vertex). -/
theorem isSplit_matchingGraph (hG : ∀ v : V, ∃ w, G.Adj v w) :
    IsSplit G (matchingGraph G) (fun d => d.fst) where
  surj := by
    intro v
    obtain ⟨w, hw⟩ := hG v
    exact ⟨⟨(v, w), hw⟩, rfl⟩
  fiber_indep := by
    intro d e hde hadj
    simp only [matchingGraph] at hadj
    subst hadj
    simp only [Dart.symm_toProd, Prod.fst_swap] at hde
    exact d.fst_ne_snd hde
  adj_proj := by
    intro d e hadj
    simp only [matchingGraph] at hadj
    subst hadj
    simp
  cover := by
    intro u v huv
    exact ⟨⟨(u, v), huv⟩, ⟨(v, u), huv.symm⟩, rfl, rfl, rfl⟩

/-- The universal splitting into a perfect matching is exclusive. -/
theorem isExclusive_matchingGraph :
    IsExclusive (matchingGraph G) (fun d : G.Dart => d.fst) := by
  intro d e z _ hne hdz hez
  simp only [matchingGraph] at hdz hez
  exact hne (Dart.symm_involutive.injective (hdz.symm.trans hez))

theorem isCograph_matchingGraph : IsCograph (matchingGraph G) :=
  isCograph_of_deg_le_one matchingGraph_deg_le_one

theorem isChordal_matchingGraph : IsChordal (matchingGraph G) :=
  isChordal_of_deg_le_one matchingGraph_deg_le_one

/-- The perfect matching produced by the universal splitting is `P_t`-free for every `t ≥ 3`;
in particular this refines the cograph (`t = 4`) statement to the whole `P_t`-free hierarchy
studied in the paper. -/
theorem isPtFree_matchingGraph (t : ℕ) (ht : 3 ≤ t) : IsPtFree (matchingGraph G) t :=
  isPtFree_of_deg_le_one t ht matchingGraph_deg_le_one

/-- The matching graph on darts is a unit interval graph: place the two darts of the `i`-th
edge at positions `3i` and `3i + 1`. -/
theorem hasUnitIntervalRep_matchingGraph [Fintype V] [LinearOrder V] :
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

/-! ## Optimality of the universal splitting among matching targets -/

/-- In a graph of maximum degree at most one, twice the number of edges is at most the number
of vertices. -/
theorem two_mul_card_edgeFinset_le_card [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (h : ∀ x y z, H.Adj x y → H.Adj x z → y = z) :
    2 * H.edgeFinset.card ≤ Fintype.card W := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc ∑ x : W, H.degree x ≤ ∑ _x : W, 1 := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        refine Finset.card_le_one.mpr fun y hy z hz => ?_
        exact h x y z (by simpa using hy) (by simpa using hz)
    _ = Fintype.card W := by simp

/-- Any splitting whose target has maximum degree at most one is automatically exclusive:
a vertex of degree at most one cannot be shared by two copies of the same vertex. -/
theorem isExclusive_of_deg_le_one {H : SimpleGraph W} {f : W → V}
    (h : ∀ x y z, H.Adj x y → H.Adj x z → y = z) : IsExclusive H f := by
  intro x y z _ hne hxz hyz
  exact hne (h z x y hxz.symm hyz.symm)

/-- **Optimality.** Any splitting of `G` whose result is a graph of maximum degree at most one
(a matching) must use at least `2|E| - |V|` splits; the universal construction
`matchingGraph` attains this bound exactly. -/
theorem two_mul_card_edgeFinset_le_of_split_matching [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] {f : W → V} (hsplit : IsSplit G H f)
    (h : ∀ x y z, H.Adj x y → H.Adj x z → y = z) :
    2 * G.edgeFinset.card ≤ Fintype.card W :=
  le_trans (Nat.mul_le_mul_left 2 hsplit.card_edgeFinset_le)
    (two_mul_card_edgeFinset_le_card h)

/-! ## The universal upper bound on splitting numbers -/

/-- **Universal splitting bound.** Every finite graph without isolated vertices can be
transformed, by an exclusive sequence of `2|E| - |V|` vertex splits, into a graph that is
simultaneously a cograph, a chordal graph and a unit interval graph. -/
theorem exists_split_cograph_chordal_unitInterval.{u} {V : Type u} (G : SimpleGraph V)
    [Fintype V] [LinearOrder V]
    [DecidableRel G.Adj] (hG : ∀ v : V, ∃ w, G.Adj v w) :
    ∃ (W' : Type u) (_ : Fintype W') (H : SimpleGraph W') (f : W' → V),
      IsSplit G H f ∧ IsExclusive H f ∧ IsCograph H ∧ IsChordal H ∧
        (∀ t, 3 ≤ t → IsPtFree H t) ∧
        HasUnitIntervalRep H ∧ Fintype.card W' = 2 * G.edgeFinset.card :=
  ⟨G.Dart, inferInstance, matchingGraph G, fun d => d.fst, isSplit_matchingGraph hG,
    isExclusive_matchingGraph, isCograph_matchingGraph, isChordal_matchingGraph,
    fun t ht => isPtFree_matchingGraph t ht,
    hasUnitIntervalRep_matchingGraph, G.dart_card_eq_twice_card_edges⟩

/-! ## Factorization of a splitting into single, shallow splits

The paper distinguishes general splittings from *shallow* ones (no newly created vertex is
split again) and from *exclusive* ones (the copies of a split vertex get disjoint
neighbourhoods).  In this section we show that the abstract model `IsSplit` loses nothing:
every splitting map factors as a chain of explicit single splits (`singleSplit`), and this
chain can always be chosen **shallow**; moreover if the splitting is exclusive (in the
projected sense below) then every single split in the chain is exclusive as well. -/

/-- A splitting is *projection-exclusive* if the copies of a vertex have neighbourhoods that
are disjoint even after projecting back to the original graph.  This is the invariant carried
by a chain of exclusive single splits, and it implies `IsExclusive`. -/
-- [dropped: platform already declares IsProjExclusive]
theorem IsProjExclusive.isExclusive {H : SimpleGraph W} {f : W → V}
    (h : IsProjExclusive H f) : IsExclusive H f :=
  fun x y z hxy hne hxz hyz => h x y z z hxy hne hxz hyz rfl

/-- The universal splitting into a perfect matching is projection-exclusive. -/
theorem isProjExclusive_matchingGraph {G : SimpleGraph V} :
    IsProjExclusive (matchingGraph G) (fun d : G.Dart => d.fst) := by
  intro d e z z' hde hne hdz hez hz
  simp only [matchingGraph] at hdz hez
  subst hdz
  subst hez
  simp only [Dart.symm_toProd, Prod.fst_swap] at hz
  exact hne (Dart.ext _ _ (Prod.ext hde hz))

universe u

/-- **One step of the factorization.**  If two distinct vertices `w₀ ≠ w₁` of `H` are copies of
the same vertex `v = f w₀` of `G`, then the splitting `f` factors through one explicit single
split of `v`: `G` splits into `singleSplit G v A B`, of which `H` is again a splitting, via a
map `g` whose fibre over the newly created vertex is exactly `{w₀}` (so the new vertex is never
split again — the step is shallow).  If `f` is projection-exclusive, then `A` and `B` are
disjoint (the step is exclusive) and `g` is again projection-exclusive. -/
theorem exists_singleSplit_factor {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V}
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

/-- `SplitChain E G H f` records that `H` is obtained from `G` by a finite chain of **single**
splits (`singleSplit`), performed **shallowly**: at each step the newly created vertex has a
singleton fibre in the rest of the chain, i.e. it is never split again.  If the parameter `E`
holds, each single split in the chain is moreover *exclusive*: the two copies receive disjoint
neighbourhoods.  The base case identifies graphs along an isomorphism. -/
-- [dropped: platform already declares SplitChain]
theorem splitChain_of_isSplit_aux {E : Prop} : ∀ (n : ℕ) {V W : Type u} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V},
    Fintype.card W - Fintype.card V ≤ n → IsSplit G H f → (E → IsProjExclusive H f) →
    SplitChain E G H f := by
  intro n
  induction n with
  | zero =>
    intro V W _ _ G H f hcard h _
    have hle : Fintype.card W ≤ Fintype.card V := by omega
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨h.surj, le_antisymm hle h.card_le⟩
    exact SplitChain.ofIso hbij (h.adj_iff_of_injective hbij.1)
  | succ n ih =>
    intro V W _ _ G H f hcard h hE
    by_cases hinj : Function.Injective f
    · exact SplitChain.ofIso ⟨hinj, h.surj⟩ (h.adj_iff_of_injective hinj)
    · obtain ⟨w₀, w₁, hfe, hne⟩ := Function.not_injective_iff.mp hinj
      obtain ⟨A, B, g, hsplit₁, hsplit₂, hfg, hnew, hdisj, hpe⟩ :=
        exists_singleSplit_factor h w₀ w₁ hne hfe.symm
      have hcs : Fintype.card (V ⊕ Unit) = Fintype.card V + 1 := by simp
      refine SplitChain.step (f w₀) A B g ?_ (fun hEt => hdisj (hE hEt)) hsplit₁
        (ih (by omega) hsplit₂ fun hEt => hpe (hE hEt)) hfg
      intro x y hx hy
      rw [(hnew x).mp hx, (hnew y).mp hy]

/-- **Every splitting is a chain of shallow single splits.**  Any splitting map between finite
graphs factors as a finite sequence of explicit one-vertex splits in which no newly created
vertex is ever split again; if the splitting is projection-exclusive, every split in the chain
is exclusive. -/
theorem SplitChain.of_isSplit {E : Prop} {V W : Type u} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V} (h : IsSplit G H f)
    (hE : E → IsProjExclusive H f) : SplitChain E G H f :=
  splitChain_of_isSplit_aux _ le_rfl h hE

/-- **The universal splitting is shallow and exclusive.**  For a finite graph without isolated
vertices, the `2|E| - |V|` splits turning `G` into the perfect matching on its darts can be
performed one vertex at a time, never splitting a newly created vertex, and with every single
split exclusive. -/
theorem splitChain_matchingGraph {V : Type u} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : ∀ v : V, ∃ w, G.Adj v w) :
    SplitChain True G (matchingGraph G) (fun d : G.Dart => d.fst) :=
  SplitChain.of_isSplit (isSplit_matchingGraph hG) fun _ => isProjExclusive_matchingGraph

/-! ## Unit interval graphs are claw-free -/

/-- `G` contains an induced claw `K_{1,3}`. -/
-- [dropped: platform already declares HasInducedClaw]
theorem not_hasInducedClaw_of_unitIntervalRep {H : SimpleGraph W}
    (h : HasUnitIntervalRep H) : ¬ HasInducedClaw H := by
  obtain ⟨p, hp⟩ := h
  rintro ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hnbc, hnbd, hncd⟩
  obtain ⟨-, hb⟩ := (hp a b).mp hab
  obtain ⟨-, hc⟩ := (hp a c).mp hac
  obtain ⟨-, hd⟩ := (hp a d).mp had
  rw [abs_le] at hb hc hd
  rcases le_or_gt (p a) (p b) with hb' | hb' <;> rcases le_or_gt (p a) (p c) with hc' | hc' <;>
      rcases le_or_gt (p a) (p d) with hd' | hd'
  · exact hnbc ((hp b c).mpr ⟨hbc, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  · exact hnbc ((hp b c).mpr ⟨hbc, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  · exact hnbd ((hp b d).mpr ⟨hbd, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  · exact hncd ((hp c d).mpr ⟨hcd, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  · exact hncd ((hp c d).mpr ⟨hcd, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  · exact hnbd ((hp b d).mpr ⟨hbd, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  · exact hnbc ((hp b c).mpr ⟨hbc, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  · exact hnbc ((hp b c).mpr ⟨hbc, abs_le.mpr ⟨by linarith, by linarith⟩⟩)

/-- An induced claw of `G` lifts to an induced claw of any zero-split (injective)
refinement. -/
theorem hasInducedClaw_of_split_injective {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V}
    (h : IsSplit G H f) (hf : Function.Injective f) (hG : HasInducedClaw G) :
    HasInducedClaw H := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hnbc, hnbd, hncd⟩ := hG
  obtain ⟨a', ha⟩ := h.surj a
  obtain ⟨b', hb⟩ := h.surj b
  obtain ⟨c', hc⟩ := h.surj c
  obtain ⟨d', hd⟩ := h.surj d
  refine ⟨a', b', c', d', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [h.adj_iff_of_injective hf, ha, hb, hc, hd, ne_eq] <;>
    first
      | assumption
      | (intro hcc; simp only [hcc] at hb hc hd; first
          | exact hbc (hb ▸ hc) | exact hbd (hb ▸ hd) | exact hcd (hc ▸ hd))

/-- If `G` contains an induced claw but the target is a unit interval graph, then at least one
split is necessary. -/
theorem card_lt_of_split_unitInterval [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {f : W → V} (h : IsSplit G H f) (hH : HasUnitIntervalRep H)
    (hG : HasInducedClaw G) : Fintype.card V < Fintype.card W := by
  rcases lt_or_eq_of_le h.card_le with hlt | heq
  · exact hlt
  · exact absurd (hasInducedClaw_of_split_injective h
      ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨h.surj, heq.symm⟩).1 hG)
      (not_hasInducedClaw_of_unitIntervalRep hH)

/-! ## Sanity checks: the forbidden structures are really present in the standard examples -/

/-- The path on four vertices. -/
-- [dropped: platform already declares pathP4]
theorem not_isCograph_pathP4 : ¬ IsCograph pathP4 := by
  intro h
  exact h ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The four-cycle. -/
-- [dropped: platform already declares cycleC4]
theorem not_isChordal_cycleC4 : ¬ IsChordal cycleC4 := by
  intro h
  exact h ⟨4, le_refl 4, id, Function.injective_id, by decide⟩

/-- The star `K_{1,3}` (the claw). -/
-- [dropped: platform already declares starK13]
theorem hasInducedClaw_starK13 : HasInducedClaw starK13 :=
  ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- The claw is not a unit interval graph, so `HasUnitIntervalRep` is a nontrivial property. -/
theorem not_hasUnitIntervalRep_starK13 : ¬ HasUnitIntervalRep starK13 :=
  fun h => not_hasInducedClaw_of_unitIntervalRep h hasInducedClaw_starK13

/-- Turning the claw into a unit interval graph requires at least one split. -/
theorem card_lt_of_split_unitInterval_starK13 [Fintype W] {H : SimpleGraph W} {f : W → Fin 4}
    (h : IsSplit starK13 H f) (hH : HasUnitIntervalRep H) : 4 < Fintype.card W := by
  have := card_lt_of_split_unitInterval h hH hasInducedClaw_starK13
  simpa using this

end VertexSplitting
section
open VertexSplitting
open SimpleGraph Finset
variable {V W X : Type*}

theorem solution [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    {f : W → V} (h : IsSplit G H f) (hH : IsCograph H) (hG : ¬ IsCograph G) :
    Fintype.card V < Fintype.card W := by
  first
  | exact VertexSplitting.card_lt_of_split_cograph h hH hG
  | exact VertexSplitting.card_lt_of_split_cograph
  | exact @VertexSplitting.card_lt_of_split_cograph _ _ G H f h hH hG
  | apply VertexSplitting.card_lt_of_split_cograph
  | exact VertexSplitting.card_lt_of_split_cograph ..


end
