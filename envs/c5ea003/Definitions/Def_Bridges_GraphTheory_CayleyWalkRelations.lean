-- Prove2me | Definitions.Def_Bridges_GraphTheory_CayleyWalkRelations
-- name    : Bridges_GraphTheory_CayleyWalkRelations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:18.015899+00:00
-- url     : https://prove2.me/theorems/808328fa-8145-4287-b911-3a43fad601d4
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_CayleyWalkRelations
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.CayleyWalkRelations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/CayleyWalkRelations.lean by skeleton subtraction
import Mathlib
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic
/-
# Closed walks in a Cayley graph are relations in the connection set

`Catalog/Bridges/GraphTheory/CayleyCharacterSpectra.lean` proves, for finite *abelian*
groups, that the number of closed `k`-walks in a Cayley graph equals `|G|` times the
number of length-`k` additive relations in the connection set, via Fourier analysis on
the Pontryagin dual.

This file proves the counting half of that statement for **every** finite group, abelian
or not, by a direct bijective/inductive argument: for any base point `x`,

```
#{closed k-walks at x} = #{(s₁,…,s_k) ∈ Sᵏ : s₁ ⋯ s_k = 1}.
```

In particular the count does not depend on the base point (a quantitative form of
vertex-transitivity), and summing over `x` gives
`#{closed k-walks} = |G| · #{length-k relations in S}`.

Together the two files say: for the whole census of Cayley graphs of finite groups, the
cycle statistics of the graph are exactly the relation counts of the connection set, and
in the abelian case those counts are computed by character sums.
-/


open Finset

namespace CayleyWalkRelations

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ## The Cayley graph of an arbitrary finite group -/

/-- The Cayley graph of a finite group with respect to a symmetric connection set `S`
avoiding the identity. -/
def cayleyGraph (S : Finset G) (hsymm : ∀ s ∈ S, s⁻¹ ∈ S) (h1 : (1 : G) ∉ S) :
    SimpleGraph G where
  Adj x y := x⁻¹ * y ∈ S
  symm := by
    intro x y h
    have := hsymm _ h
    simpa using this
  loopless := ⟨fun x h => h1 (by simpa using h)⟩

instance instDecidableAdj (S : Finset G) (hsymm : ∀ s ∈ S, s⁻¹ ∈ S) (h1 : (1 : G) ∉ S) :
    DecidableRel (cayleyGraph S hsymm h1).Adj :=
  fun x y => decidable_of_iff (x⁻¹ * y ∈ S) Iff.rfl


/-! ## Step tuples, relations, and path counts -/

/-- All `k`-tuples of steps taken from `S`. -/
def stepTuples (S : Finset G) (k : ℕ) : Finset (Fin k → G) := Fintype.piFinset fun _ => S

/-- The number of length-`k` relations in `S`: tuples `(s₁,…,s_k) ∈ Sᵏ` whose product,
taken in order, is the identity. -/
def relationCount (S : Finset G) (k : ℕ) : ℕ :=
  ((stepTuples S k).filter fun p => (List.ofFn p).prod = 1).card

/-- The number of `k`-step routes from `x` to `y` with all steps in `S`. -/
def pathCount (S : Finset G) (k : ℕ) (x y : G) : ℕ :=
  ((stepTuples S k).filter fun p => x * (List.ofFn p).prod = y).card








/-! ## The bridge -/





/-! ## A nonabelian worked example -/

/-- The three transpositions of `S₃`. -/
def transS3 : Finset (Equiv.Perm (Fin 3)) := Finset.univ.filter (fun g => g ≠ 1 ∧ g * g = 1)





end CayleyWalkRelations


