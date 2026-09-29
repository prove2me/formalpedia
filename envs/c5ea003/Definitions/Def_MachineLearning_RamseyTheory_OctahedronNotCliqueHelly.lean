-- Prove2me | Definitions.Def_MachineLearning_RamseyTheory_OctahedronNotCliqueHelly
-- name    : MachineLearning_RamseyTheory_OctahedronNotCliqueHelly
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:56:19.129195+00:00
-- url     : https://prove2.me/theorems/69b1eea6-2cd8-465d-9ae7-242f5c1e96aa
-- title:
--   Aether Catalog definitions — MachineLearning_RamseyTheory_OctahedronNotCliqueHelly
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.RamseyTheory.OctahedronNotCliqueHelly`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/RamseyTheory/OctahedronNotCliqueHelly.lean by skeleton subtraction
import Mathlib

/-!
# The octahedron graph `K_{2,2,2}` is not clique-Helly

This file gives a self-contained, minimal formalization of the fact that the
octahedron graph (the complete tripartite graph `K_{2,2,2}`) is **not**
clique-Helly.

The vertex set is `Fin 6`, split into three parts of size two according to
`i / 2`:

* part `0` = `{0, 1}`,
* part `1` = `{2, 3}`,
* part `2` = `{4, 5}`.

Two vertices are adjacent iff they are distinct and lie in different parts.

A graph is *clique-Helly* if every family of maximal cliques that pairwise
intersect has a common vertex.  We exhibit three maximal cliques
`{0,2,4}`, `{0,3,5}`, `{1,2,5}` that pairwise intersect but have empty total
intersection, witnessing the failure of the Helly property.
-/

open SimpleGraph

/-- The octahedron graph `K_{2,2,2}` on `Fin 6`, with parts `{0,1}`, `{2,3}`,
`{4,5}` determined by `i / 2`.  Two vertices are adjacent iff they are distinct
and lie in different parts. -/
def octahedron : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧ i.val / 2 ≠ j.val / 2
  symm := fun _ _ h => ⟨h.1.symm, fun e => h.2 e.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `S` is a maximal clique of `G`: it is a clique and no strictly larger set is
a clique. -/
def IsMaxClique {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsClique S ∧ ∀ T, S ⊂ T → ¬ G.IsClique T

/-- `G` is clique-Helly: every family of maximal cliques that pairwise intersect
has a nonempty common intersection. -/
def CliqueHelly {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ Ss : Set (Set V), (∀ s ∈ Ss, IsMaxClique G s) →
    (∀ s₁ ∈ Ss, ∀ s₂ ∈ Ss, (s₁ ∩ s₂).Nonempty) → (⋂ s ∈ Ss, s).Nonempty


