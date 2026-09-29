-- Prove2me | Definitions.Def_Combinatorics_ChromaticPolynomialTheory
-- name    : Combinatorics_ChromaticPolynomialTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:30:15.638456+00:00
-- url     : https://prove2.me/theorems/3fc95297-cab9-4660-8845-ced47701809a
-- title:
--   Aether Catalog definitions — Combinatorics_ChromaticPolynomialTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.ChromaticPolynomialTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/ChromaticPolynomialTheory.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chromatic Polynomials and Deletion–Contraction

This file develops the *chromatic counting function* of a finite simple graph: for `q : ℕ`,
`chromVal G q` is the number of proper colorings `V → Fin q` of `G`.  This is the value at `q`
of the chromatic polynomial `P(G, q)`.

Mathlib provides `SimpleGraph.Coloring`, `SimpleGraph.Colorable`, and `SimpleGraph.chromaticNumber`,
but it does **not** provide the chromatic polynomial, the deletion–contraction recurrence, or the
closed-form evaluations for the empty and complete graphs.  We fill these gaps:

  * `chromVal_bot`     :  `P(Ē_n, q) = q ^ n`            (the empty graph),
  * `chromVal_top`     :  `P(K_n, q) = q^{\underline n}` (the complete graph, falling factorial),
  * `deletion_contraction` :
        `P(G − e, q) = P(G, q) + P(G / e, q)`
    for every edge `e = {a,b}` of `G`, where `G − e` deletes `e` and `G / e` contracts it.

The deletion–contraction recurrence is the structural engine behind the entire theory of
chromatic polynomials (e.g. Whitney's broken-circuit theorem and the fact that `P(G,·)` is a
polynomial with alternating-sign integer coefficients).

-- !-- Lab Notes -- !--
HYPOTHESIS.  Counting proper colorings should satisfy `P(G−e) = P(G) + P(G/e)`: a proper coloring of
`G−e` either gives the endpoints of `e` distinct colors (these are exactly the proper colorings of
`G`) or equal colors (these are exactly the proper colorings of the contraction `G/e`).

EXPERIMENTAL PLAN.
  (1) Define `delEdge G a b` (delete the single edge `{a,b}`) and `contract G a b` (merge `b` into
      `a`, on the vertex set `{v // v ≠ b}`), both as honest `SimpleGraph`s with decidable adjacency.
  (2) Show `{proper colorings of G−e with `c a ≠ c b`} = {proper colorings of G}` as finsets.
  (3) Build an explicit bijection `{proper colorings of G−e with `c a = c b`} ≃ {proper colorings
      of G/e}` by restriction/extension along `{v // v ≠ b} ↪ V`.
  (4) Split `P(G−e)` by the decidable predicate `c a = c b` and assemble (2)+(3).

INSIGHT.  Modeling the contraction on the subtype `{v // v ≠ b}` (rather than a quotient) keeps
adjacency decidable and makes the coloring bijection a concrete restrict/extend pair, avoiding all
quotient bookkeeping.  The merged vertex's incidences are encoded by redirecting `b`'s neighbors to
`a` in `contract`'s adjacency relation.
-- !-- End Lab Notes -- !--
-/


namespace Catalog.Combinatorics.ChromaticPolynomial

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Proper colorings as a finset of functions -/

/-- The finset of proper `α`-colorings of `G`, viewed as functions `V → α`.
A function is proper when adjacent vertices receive different colors. -/
def properColorings (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : Type*) [Fintype α] [DecidableEq α] : Finset (V → α) :=
  Finset.univ.filter (fun c => ∀ x y, G.Adj x y → c x ≠ c y)

lemma mem_properColorings {G : SimpleGraph V} [DecidableRel G.Adj]
    {α : Type*} [Fintype α] [DecidableEq α] (c : V → α) :
    c ∈ properColorings G α ↔ ∀ x y, G.Adj x y → c x ≠ c y := by
  simp [properColorings]

/-- The chromatic counting function: the number of proper colorings of `G` with `q` colors,
i.e. the value `P(G, q)` of the chromatic polynomial. -/
def chromVal (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) : ℕ :=
  (properColorings G (Fin q)).card

/-! ## Edge deletion and contraction as honest graphs -/

/-- Delete the single edge `{a, b}` from `G`. -/
def delEdge (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))
  symm := by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact h.2 (Or.inr ⟨hy, hx⟩)
    · exact h.2 (Or.inl ⟨hy, hx⟩)
  loopless := ⟨fun x h => G.irrefl h.1⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    DecidableRel (delEdge G a b).Adj := by
  intro x y
  show Decidable (G.Adj x y ∧ ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))
  infer_instance

/-- Contract the edge `{a, b}` of `G` by merging `b` into `a`.  The vertex set is `{v // v ≠ b}`;
adjacency between `x` and `y` holds when `x ≠ y` and either they are adjacent in `G`, or one of them
is `a` and the other is a `G`-neighbor of `b` (encoding the merged vertex's incidences). -/
def contract (G : SimpleGraph V) (a b : V) : SimpleGraph {v : V // v ≠ b} where
  Adj x y := x ≠ y ∧ (G.Adj x.1 y.1 ∨ (G.Adj x.1 b ∧ y.1 = a) ∨ (G.Adj y.1 b ∧ x.1 = a))
  symm := by
    rintro x y ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := ⟨fun x h => h.1 rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    DecidableRel (contract G a b).Adj := by
  intro x y
  show Decidable (x ≠ y ∧ (G.Adj x.1 y.1 ∨ (G.Adj x.1 b ∧ y.1 = a) ∨ (G.Adj y.1 b ∧ x.1 = a)))
  infer_instance

/-! ## Evaluations on the empty and complete graphs -/

/-
**Empty graph.** `P(Ē_n, q) = q ^ n`: every function is a proper coloring of the edgeless
graph.
-/

/-
**Complete graph.** `P(K_n, q) = q^{\underline n}` (the falling factorial): the proper
colorings of the complete graph are exactly the injective functions `V → Fin q`.
-/

/-! ## Deletion–contraction -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-
The proper colorings of `G − e` that give the endpoints of `e` *distinct* colors are exactly
the proper colorings of `G`.
-/

/-
The proper colorings of `G − e` that give the endpoints of `e` *equal* colors are in bijection
with the proper colorings of the contraction `G / e`; hence the cardinalities agree.
-/

/-
**Deletion–contraction for the chromatic polynomial.**
For every edge `e = {a, b}` of `G`,
`P(G − e, ·) = P(G, ·) + P(G / e, ·)` (counted with `α` colors).
-/

/-
The same recurrence specialized to the chromatic counting function with `q` colors.
-/

/-
-- !-- Lab Notes (synthesis & critique) -- !--
OUTCOMES.
  * `chromVal_bot` / `chromVal_top`: the edgeless graph gives `q^n` (all functions proper) and the
    complete graph gives the falling factorial `q^{\underline n}` (proper colorings = injections =
    embeddings, via `Fintype.card_embedding_eq`).
  * `deletion_contraction`: the headline result. Splitting the proper colorings of `G - e` by the
    decidable predicate `c a = c b` separates them into the proper colorings of `G` (endpoints get
    distinct colors, `properColorings_delEdge_filter_ne`) and the proper colorings of the contraction
    `G / e` (endpoints get equal colors, `card_delEdge_filter_eq`).
  * The contraction bijection (`card_delEdge_filter_eq`) is the technical core: restrict a coloring to
    `{v // v ≠ b}` in one direction and re-extend `b ↦ a`'s color in the other; properness transfers
    because `contract`'s adjacency redirects `b`'s neighbors to `a`.

CRITIQUE / ADVERSARIAL REVIEW.
  * None of the main theorems is vacuous: `chromVal_top` is a nonconstant closed form, and
    deletion–contraction is verified numerically (P₃ = K₃ − e gives 12 = 6 + 6 at q = 3).
  * Edge case `a = b` is excluded automatically since the recurrence hypothesis is `G.Adj a b`, which
    forces `a ≠ b`; the contraction's domain `{v // v ≠ b}` is then nondegenerate.
  * The contraction is modeled on a subtype rather than a quotient; this is faithful because proper
    colorings only see *which* vertices are merged, and merging `b` into `a` with redirected
    incidences reproduces exactly the colorings with `c a = c b`.

VERIFICATION.  `#print axioms deletion_contraction` = [propext, Classical.choice, Quot.sound]; the
file compiles with 0 sorries.
-- !-- End Lab Notes -- !--
-/


/-! ## Multiplicativity on disjoint unions -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The disjoint union of two simple graphs, represented on the sum of their vertex types. -/
def disjointUnion (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (Sum V W) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inr a, Sum.inr b => H.Adj a b
    | _, _ => False
  symm := by
    intro x y h
    cases x <;> cases y <;> simp_all [SimpleGraph.adj_comm]
  loopless := by
    constructor
    intro x h
    cases x <;> simp_all

instance (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    DecidableRel (disjointUnion G H).Adj := by
  intro x y
  cases x <;> cases y <;> simp [disjointUnion] <;> infer_instance

/-- Proper colorings of a disjoint union are in bijection with pairs of proper
colorings of its two components. -/
def properColoringsDisjointUnionEquiv (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) :
    {c // c ∈ properColorings (disjointUnion G H) (Fin q)} ≃
      {c // c ∈ properColorings G (Fin q)} × {c // c ∈ properColorings H (Fin q)} := by
  refine ⟨fun ⟨c, hc⟩ => ⟨⟨fun v => c (Sum.inl v), ?_⟩, ⟨fun w => c (Sum.inr w), ?_⟩⟩,
          fun ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ => ⟨fun x => x.elim c₁ c₂, ?_⟩, ?_, ?_⟩
  · rw [mem_properColorings] at hc ⊢
    intro x y hxy
    exact hc (Sum.inl x) (Sum.inl y) (by simp [disjointUnion, hxy])
  · rw [mem_properColorings] at hc ⊢
    intro x y hxy
    exact hc (Sum.inr x) (Sum.inr y) (by simp [disjointUnion, hxy])
  · rw [mem_properColorings] at hc₁ hc₂ ⊢
    intro x y hxy
    cases x <;> cases y <;> simp_all [disjointUnion]
  · intro ⟨c, hc⟩; simp [properColorings] at hc ⊢
    ext x; cases x <;> rfl
  · intro ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩; simp [properColorings] at hc₁ hc₂ ⊢




end Catalog.Combinatorics.ChromaticPolynomial


