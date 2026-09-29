-- Prove2me | Definitions.Def_Geometry_PosetTwinWidth_LinearBound
-- name    : Geometry_PosetTwinWidth_LinearBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:37:59.750457+00:00
-- url     : https://prove2.me/theorems/e54552bd-a119-454f-99d9-3f346b70241b
-- title:
--   Aether Catalog definitions — Geometry_PosetTwinWidth_LinearBound
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PosetTwinWidth.LinearBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PosetTwinWidth/LinearBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_Contractions
import Definitions.Def_Geometry_PosetTheory_NonCircular
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
/-!
# A linear contraction sequence for finite posets of bounded width

## Strategy

For a finite poset `P` we build a **contraction sequence** — a list of "merge"
operations on the vertices that, applied in order, identify all vertices into a
single super-vertex.  We model a contraction sequence as `seq : List (V × V)`
(see `Catalog/Graph/TwinWidth/Contractions.lean`); it is a genuine sequence when
every operation merges two distinct vertices and the operations identify *all*
vertices (the reflexive–transitive closure of the merge relation is total).

The construction proceeds in two reusable steps:

1. **Order the vertices without self-reference.**  Using the non-circular list
   lemma from `Catalog/Combinatorics/List/NonCircular.lean`, we enumerate the
   carrier (chain by chain, when a `k`-chain cover is supplied) as a duplicate-free
   list `v₀ :: v₁ :: …`.  Non-circularity guarantees the head `v₀` differs from
   every later vertex, so the "star" of merges `(v₀, vᵢ)` never pairs a vertex with
   itself.

2. **Contract along that order.**  We invoke the generic
   `Graph.TwinWidth.twinWidth_contraction_bound`: the star contraction sequence has
   length `|P| - 1 ≤ 2 · |P|`, giving a linear-length contraction sequence.

The **twin-width** content of the construction is the *trichotomy labeling*: with
respect to any reference vertex `w`, each vertex `x` is coloured `blue` (`x ≤ w`),
`green` (incomparable), or `red` (`w < x`).  Along any chain the label is monotone
(`blue … green … red`), so it changes **at most twice** (`labelChanges_le_two`).
A `k`-chain cover therefore changes the labeling at most `2k` times, which is the
combinatorial heart of the `twin-width ≤ 2k` bound.

## Main results

* `FinitePoset.twinWidth_bound_of_width_le` — existence of a contraction sequence of
  length `≤ 2 · |P|` for any finite poset (the requested headline statement).
* `FinitePoset.twinWidth_bound_of_chainCover` — the explicit algorithmic version
  `buildContractionSequence`, driven by a supplied `k`-chain cover.
* `FinitePoset.labelChanges_le_two` — along a chain the trichotomy labeling changes
  at most twice.

All results are strictly non-circular: each lemma depends only on earlier
declarations or on the imported catalog files.
-/

open Graph.TwinWidth

namespace Geometry.PosetTwinWidth

/-- A finite poset: a finite, decidably-ordered partial order. -/
structure FinitePoset where
  /-- The underlying set of elements. -/
  carrier : Type
  [ftype : Fintype carrier]
  [deq : DecidableEq carrier]
  /-- The order relation. -/
  le : carrier → carrier → Prop
  [dle : DecidableRel le]
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b

attribute [instance] FinitePoset.ftype FinitePoset.deq FinitePoset.dle

namespace FinitePoset

variable (P : FinitePoset)

/-- The number of elements of the poset. -/
def card : ℕ := Fintype.card P.carrier

/-- Two elements are comparable when one is `≤` the other. -/
def comparable (a b : P.carrier) : Prop := P.le a b ∨ P.le b a

instance (a b : P.carrier) : Decidable (P.comparable a b) := by
  unfold comparable; infer_instance

/-- A finite subset is an antichain when its distinct elements are pairwise
incomparable. -/
def IsAntichainF (s : Finset P.carrier) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ P.comparable a b

/-- The **width** of `P`: the maximum size of an antichain. -/
noncomputable def width : ℕ := by
  classical
  exact (Finset.univ.powerset.filter (fun s => P.IsAntichainF s)).sup Finset.card

/-! ### Trichotomy labeling -/

/-- The three labels used to colour vertices relative to a reference vertex. -/
inductive Tri where
  | blue
  | green
  | red
  deriving DecidableEq

/-- The trichotomy labeling of `x` relative to a reference vertex `w`:
`blue` if `x ≤ w`, `red` if `w < x` (i.e. `w ≤ x` but not `x ≤ w`), and `green`
otherwise (incomparable). -/
def label (w x : P.carrier) : Tri :=
  if P.le x w then Tri.blue
  else if P.le w x then Tri.red
  else Tri.green

/-- The number of times a `Tri`-valued labeling changes between adjacent entries
of a list. -/
def labelChanges {α : Type*} (f : α → Tri) : List α → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if f a = f b then 0 else 1) + labelChanges f (b :: rest)

/-! ### Chain covers -/

/-- A **`k`-chain cover** of `P`: an assignment of each element to one of `k` chains
such that any two elements in the same chain are comparable. -/
structure ChainCover (k : ℕ) where
  /-- The chain index assigned to each element. -/
  idx : P.carrier → Fin k
  /-- Elements in the same chain are comparable. -/
  isChain : ∀ a b, idx a = idx b → P.comparable a b

/-! ### The contraction sequence predicate -/

/-- `IsTwinWidthContractionSequence seq P` states that `seq` is a contraction
sequence of `P`: it lives on the carrier, every operation merges two *distinct*
vertices (no self-reference), and the operations identify *all* vertices into a
single final super-vertex (the reflexive–transitive closure of the merge relation
is total). -/
def IsTwinWidthContractionSequence {V : Type} (seq : List (V × V)) (P : FinitePoset) : Prop :=
  V = P.carrier ∧
    (∀ e ∈ seq, e.1 ≠ e.2) ∧
    (∀ a b : V, Relation.ReflTransGen (MergeRel seq) a b)

/-! ### The construction -/

/-- The non-circular enumeration of the `i`-th chain of a cover. -/
noncomputable def chainList {k : ℕ} (C : P.ChainCover k) (i : Fin k) : List P.carrier :=
  Combinatorics.NonCircular.order (Finset.univ.filter (fun v => C.idx v = i))

/-- Enumerate all vertices, chain by chain, as a single non-circular list. -/
noncomputable def orderByChains {k : ℕ} (C : P.ChainCover k) : List P.carrier :=
  ((List.finRange k).map (fun i => P.chainList C i)).flatten

/-- **The algorithm.**  Given a poset together with a `k`-chain cover, return the
star contraction sequence obtained by ordering the vertices chain by chain and
contracting everything into the first vertex. -/
noncomputable def buildContractionSequence {k : ℕ} (C : P.ChainCover k) :
    List (P.carrier × P.carrier) :=
  starSequence (P.orderByChains C)

/-! ### Properties of the chain ordering -/





/-! ### The trichotomy labeling changes at most twice along a chain -/

/-- A numerical rank of the three labels: `blue < green < red`. -/
def triStage : Tri → ℕ
  | Tri.blue => 0
  | Tri.green => 1
  | Tri.red => 2





/-! ### Main results -/



end FinitePoset

end Geometry.PosetTwinWidth


