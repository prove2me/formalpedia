-- Prove2me | Definitions.Def_Bridges_VertexSplittingExact
-- name    : Bridges_VertexSplittingExact
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:54.285368+00:00
-- url     : https://prove2.me/theorems/c9a0722a-5cfe-4373-975a-f6bd22d7455c
-- title:
--   Aether Catalog definitions — Bridges_VertexSplittingExact
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.VertexSplittingExact`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/VertexSplittingExact.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_VertexSplitting
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Exact splitting numbers for the smallest obstructions

This file complements `Bridges.VertexSplitting`, where the general theory of the vertex
splitting operation of *Hardness of Vertex Splitting: Cographs, Chordal Graphs, and Beyond*
is developed, with **exact** values of the splitting number for the smallest obstructions of
each of the three target classes studied there.

Main results:

* `isChordal_of_unitIntervalRep`: unit interval graphs are chordal (so the unit-interval
  splitting number always dominates the chordal one).
* `cograph_split_pathP4_exact`: the cograph splitting number of `P₄` is exactly one, and the
  single split can be taken exclusive.
* `chordal_split_cycleC4_exact`: the chordal splitting number of `C₄` is exactly one.
* `unitInterval_split_starK13_exact`: the unit-interval splitting number of the claw `K_{1,3}`
  is exactly one.
* `unitInterval_split_starK14_exact`: the unit-interval splitting number of `K_{1,4}` is also
  exactly one.  In particular the guess that `K_{1,n}` needs `n - 2` splits is false already
  for `n = 4`: pairing the leaves shows `⌈n/2⌉ - 1` splits suffice.
* `card_ge_of_split_clawFree_star` and `unitInterval_split_star_exact`: for every `n ≥ 1` the
  unit-interval splitting number of the star `K_{1,n}` is exactly `⌈n/2⌉ - 1`, by an exclusive
  splitting into `⌈n/2⌉` disjoint short paths, and a matching counting lower bound valid for
  every claw-free target.
-/

namespace VertexSplitting

open SimpleGraph

/-! ## Unit interval graphs are chordal -/


/-! ## `P₄`: one split makes a cograph -/

/-- The graph obtained from `P₄ = 0-1-2-3` by splitting the vertex `1` into `1` (keeping the
neighbour `0`) and `4` (keeping the neighbour `2`).  It is the disjoint union of an edge and a
path on three vertices. -/
def splitP4 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 4 ∧ j = 2) ∨ (i = 2 ∧ j = 3))

instance : DecidableRel splitP4.Adj := fun _ _ => by
  unfold splitP4 SimpleGraph.fromRel
  infer_instance

/-- The origin map of `splitP4`: the new vertex `4` is a copy of `1`. -/
def splitMapP4 : Fin 5 → Fin 4 := ![0, 1, 2, 3, 1]





/-! ## `C₄`: one split makes a chordal graph -/

/-- The path on five vertices `0-1-2-3-4`. -/
def pathP5 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun i j => (i : ℕ) + 1 = (j : ℕ))

instance : DecidableRel pathP5.Adj := fun _ _ => by
  unfold pathP5 SimpleGraph.fromRel
  infer_instance



/-- Splitting the vertex `0` of the four-cycle `0-1-2-3-0` unfolds it into the path
`0-1-2-3-4`, where `4` is the second copy of `0`. -/
def splitMapC4 : Fin 5 → ZMod 4 := ![0, 1, 2, 3, 0]




/-! ## Stars: one split makes `K_{1,3}` and `K_{1,4}` unit interval graphs -/

/-- Splitting the centre of the claw `K_{1,3}` into the vertex `0` (keeping the leaves `1, 2`)
and the vertex `4` (keeping the leaf `3`) gives the disjoint union of `P₃` and an edge. -/
def splitK13 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ (i = 4 ∧ j = 3))

instance : DecidableRel splitK13.Adj := fun _ _ => by
  unfold splitK13 SimpleGraph.fromRel
  infer_instance

/-- The origin map of `splitK13`: the new vertex `4` is a second copy of the centre `0`. -/
def splitMapK13 : Fin 5 → Fin 4 := ![0, 1, 2, 3, 0]





/-- The star `K_{1,4}` with centre `0` and leaves `1, 2, 3, 4`. -/
def starK14 : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun i j => i = 0 ∧ j ≠ 0)

instance : DecidableRel starK14.Adj := fun _ _ => by
  unfold starK14 SimpleGraph.fromRel
  infer_instance


/-- Splitting the centre of `K_{1,4}` into `0` (keeping the leaves `1, 2`) and `5` (keeping the
leaves `3, 4`) gives the disjoint union of two paths on three vertices. -/
def splitK14 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ (i = 5 ∧ (j = 3 ∨ j = 4)))

instance : DecidableRel splitK14.Adj := fun _ _ => by
  unfold splitK14 SimpleGraph.fromRel
  infer_instance

/-- The origin map of `splitK14`: the new vertex `5` is a second copy of the centre `0`. -/
def splitMapK14 : Fin 6 → Fin 5 := ![0, 1, 2, 3, 4, 0]





/-! ## A general lower bound for stars

The claw `K_{1,3}` is the smallest obstruction to being a unit interval graph, and a star
`K_{1,n}` contains many of them.  Since claw-free graphs let every copy of the centre keep at
most two leaves, at least `⌈n/2⌉` copies of the centre are needed.
-/

/-- The star `K_{1,n}`: the centre is the vertex `0` and the leaves are `1, …, n`. -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun i j => i = 0 ∧ j ≠ 0)





/-! ### The matching upper bound for stars

Pairing up the leaves gives a splitting of `K_{1,n}` into `⌈n/2⌉` disjoint paths (`P₃`s, and one
`P₂` if `n` is odd), which is a unit interval graph.  Together with
`card_ge_of_split_clawFree_star` this determines the unit-interval splitting number of every
star exactly.
-/

/-- The disjoint union of `m` stars with at most two leaves each: the leaf `i` is attached to the
centre copy `⌊i/2⌋`. -/
def starSplitGraph (n m : ℕ) : SimpleGraph (Fin n ⊕ Fin m) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | Sum.inl i, Sum.inr j => (i : ℕ) / 2 = (j : ℕ)
    | _, _ => False)

/-- The origin map: the leaf `i` comes from the leaf `i + 1` of the star, every centre copy comes
from the centre `0`. -/
def starSplitMap (n m : ℕ) : Fin n ⊕ Fin m → Fin (n + 1) :=
  Sum.elim Fin.succ (fun _ => 0)






end VertexSplitting


