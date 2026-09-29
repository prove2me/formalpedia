-- Prove2me | Definitions.Def_Bridges_VertexSplitting
-- name    : Bridges_VertexSplitting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:18.879414+00:00
-- url     : https://prove2.me/theorems/aba90049-c72d-43e4-9c60-5dbca7b2c6b8
-- title:
--   Aether Catalog definitions — Bridges_VertexSplitting
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.VertexSplitting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/VertexSplitting.lean by skeleton subtraction
import Mathlib
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

/-- `IsSplit G H f` says that the graph `H` (on vertex type `W`) is obtained from `G`
(on vertex type `V`) by a sequence of vertex splits, with `f` recording, for each vertex of `H`,
the vertex of `G` it descends from. -/
structure IsSplit (G : SimpleGraph V) (H : SimpleGraph W) (f : W → V) : Prop where
  /-- No vertex of `G` disappears. -/
  surj : Function.Surjective f
  /-- The copies of a vertex form an independent set. -/
  fiber_indep : ∀ x y, f x = f y → ¬ H.Adj x y
  /-- Splitting creates no new adjacencies. -/
  adj_proj : ∀ x y, H.Adj x y → G.Adj (f x) (f y)
  /-- The neighbourhoods of the copies of `u` together cover `N(u)`. -/
  cover : ∀ u v, G.Adj u v → ∃ x y, f x = u ∧ f y = v ∧ H.Adj x y

/-- A splitting is *exclusive* if the neighbourhoods of the copies of a vertex are pairwise
disjoint. -/
def IsExclusive (H : SimpleGraph W) (f : W → V) : Prop :=
  ∀ x y z, f x = f y → x ≠ y → H.Adj x z → ¬ H.Adj y z



/-! ## Basic invariants -/




/-! ## The one-step split -/

/-- Adjacency of the graph obtained from `G` by splitting the vertex `v` into two copies,
the first one (`Sum.inl v`) keeping the neighbours in `A` and the second one (`Sum.inr ()`)
keeping the neighbours in `B`. -/
def splitAdj (G : SimpleGraph V) (v : V) (A B : Set V) : V ⊕ Unit → V ⊕ Unit → Prop
  | Sum.inl x, Sum.inl y => G.Adj x y ∧ (x = v → y ∈ A) ∧ (y = v → x ∈ A)
  | Sum.inl x, Sum.inr _ => x ∈ B
  | Sum.inr _, Sum.inl y => y ∈ B
  | Sum.inr _, Sum.inr _ => False

/-- The graph obtained from `G` by a single split of the vertex `v`, where the two copies
inherit the neighbours in `A` and in `B` respectively. -/
def singleSplit (G : SimpleGraph V) (v : V) (A B : Set V) : SimpleGraph (V ⊕ Unit) where
  Adj := splitAdj G v A B
  symm := by
    rintro (x | x) (y | y) h <;> simp only [splitAdj] at h ⊢
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩
    · exact h
    · exact h
  loopless := ⟨by
    rintro (x | x) h <;> simp only [splitAdj] at h
    exact G.irrefl h.1⟩

/-- The map recording the origin of each vertex of a one-step split. -/
def splitMap (v : V) : V ⊕ Unit → V := Sum.elim id (fun _ => v)




/-! ## Target graph classes -/

/-- `G` contains an induced path on four vertices. -/
def HasInducedP4 (G : SimpleGraph V) : Prop :=
  ∃ a b c d, G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d ∧ ¬ G.Adj a d

/-- Cographs are exactly the `P₄`-free graphs. -/
def IsCograph (G : SimpleGraph V) : Prop := ¬ HasInducedP4 G

/-- `G` contains an induced cycle of length at least `4`. -/
def HasLongInducedCycle (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (_ : 4 ≤ k) (c : ZMod k → V), Function.Injective c ∧
    ∀ i j, G.Adj (c i) (c j) ↔ (j = i + 1 ∨ i = j + 1)

/-- Chordal graphs are exactly the graphs without induced cycles of length at least `4`. -/
def IsChordal (G : SimpleGraph V) : Prop := ¬ HasLongInducedCycle G

/-- `G` is a unit interval graph: its vertices can be placed on the real line so that two
distinct vertices are adjacent exactly when their unit intervals meet. -/
def HasUnitIntervalRep (G : SimpleGraph V) : Prop :=
  ∃ p : V → ℝ, ∀ x y, G.Adj x y ↔ (x ≠ y ∧ |p x - p y| ≤ 1)



/-! ## `P_t`-freeness -/

/-- `G` contains an induced path on `t` vertices. -/
def HasInducedPath (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ p : Fin t → V, Function.Injective p ∧
    ∀ i j : Fin t, G.Adj (p i) (p j) ↔ ((i : ℕ) + 1 = (j : ℕ) ∨ ((j : ℕ) + 1 = (i : ℕ)))

/-- `G` is `P_t`-free. -/
def IsPtFree (G : SimpleGraph V) (t : ℕ) : Prop := ¬ HasInducedPath G t



/-! ## Transfer of forbidden structures along injective splitting maps -/





/-! ## The universal splitting: turning any graph into a perfect matching -/

variable (G : SimpleGraph V)

/-- Splitting every vertex `v` of `G` into `deg v` copies, one for each incident edge, yields
the perfect matching on the darts of `G`: two darts are adjacent exactly when they are the two
orientations of the same edge. -/
def matchingGraph : SimpleGraph G.Dart where
  Adj d e := e = d.symm
  symm := by
    intro d e h
    subst h
    simp
  loopless := ⟨by
    intro d h
    exact (Dart.symm_ne d) h.symm⟩

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

/-- A splitting is *projection-exclusive* if the copies of a vertex have neighbourhoods that
are disjoint even after projecting back to the original graph.  This is the invariant carried
by a chain of exclusive single splits, and it implies `IsExclusive`. -/
def IsProjExclusive (H : SimpleGraph W) (f : W → V) : Prop :=
  ∀ x y z z', f x = f y → x ≠ y → H.Adj x z → H.Adj y z' → f z ≠ f z'



universe u


/-- `SplitChain E G H f` records that `H` is obtained from `G` by a finite chain of **single**
splits (`singleSplit`), performed **shallowly**: at each step the newly created vertex has a
singleton fibre in the rest of the chain, i.e. it is never split again.  If the parameter `E`
holds, each single split in the chain is moreover *exclusive*: the two copies receive disjoint
neighbourhoods.  The base case identifies graphs along an isomorphism. -/
inductive SplitChain (E : Prop) :
    {V : Type u} → SimpleGraph V → {W : Type u} → SimpleGraph W → (W → V) → Prop
  | ofIso {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V} :
      Function.Bijective f → (∀ x y, H.Adj x y ↔ G.Adj (f x) (f y)) → SplitChain E G H f
  | step {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V}
      (v : V) (A B : Set V) (g : W → V ⊕ Unit)
      (hnew : ∀ x y, g x = Sum.inr () → g y = Sum.inr () → x = y)
      (hdisj : E → ∀ u ∈ A, u ∉ B)
      (hsplit : IsSplit G (singleSplit G v A B) (splitMap v))
      (hrest : SplitChain E (singleSplit G v A B) H g)
      (hf : f = splitMap v ∘ g) : SplitChain E G H f




/-! ## Unit interval graphs are claw-free -/

/-- `G` contains an induced claw `K_{1,3}`. -/
def HasInducedClaw (G : SimpleGraph V) : Prop :=
  ∃ a b c d, G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ¬ G.Adj b c ∧ ¬ G.Adj b d ∧ ¬ G.Adj c d




/-! ## Sanity checks: the forbidden structures are really present in the standard examples -/

/-- The path on four vertices. -/
def pathP4 : SimpleGraph (Fin 4) := SimpleGraph.fromRel (fun i j => (i : ℕ) + 1 = (j : ℕ))

instance : DecidableRel pathP4.Adj := fun _ _ => by
  unfold pathP4 SimpleGraph.fromRel
  infer_instance


/-- The four-cycle. -/
def cycleC4 : SimpleGraph (ZMod 4) := SimpleGraph.fromRel (fun i j => j = i + 1)

instance : DecidableRel cycleC4.Adj := fun _ _ => by
  unfold cycleC4 SimpleGraph.fromRel
  infer_instance


/-- The star `K_{1,3}` (the claw). -/
def starK13 : SimpleGraph (Fin 4) := SimpleGraph.fromRel (fun i j => i = 0 ∧ j ≠ 0)

instance : DecidableRel starK13.Adj := fun _ _ => by
  unfold starK13 SimpleGraph.fromRel
  infer_instance




end VertexSplitting


