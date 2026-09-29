-- Prove2me | Definitions.Def_Geometry_RomanDomination_ConvexBipartite
-- name    : Geometry_RomanDomination_ConvexBipartite
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:53:39.177175+00:00
-- url     : https://prove2.me/theorems/01f1c834-68fd-4b3c-865f-3473b8d0a2ba
-- title:
--   Aether Catalog definitions — Geometry_RomanDomination_ConvexBipartite
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.RomanDomination.ConvexBipartite`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/RomanDomination/ConvexBipartite.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_RomanDomination_Variants
/-
# Convex bipartite graphs and exact Roman-type domination numbers of `K_{m,n}`

A bipartite graph with parts `A` and `B` is **convex** (with respect to a linear
order on `A`) when the neighbourhood of every vertex of `B` is an order-convex
subset of `A`, i.e. an interval.  This interval structure is exactly what makes the
left-to-right dynamic programming algorithms for Roman-type domination possible on
this graph class.

Here we

* define `IsConvexBipartite` for graphs on `Fin m ⊕ Fin n`,
* show that a convex bipartite graph is `2`-colourable,
* show that the complete bipartite graph `K_{m,n}` is convex bipartite, and
* compute *exactly* the Roman domination number and the Italian (Roman-`{2}`)
  domination number of `K_{m,n}`:

```
γ_R(K_{m,n}) = min 4 (min (m+1) (n+1))     (m, n ≥ 1)
γ_I(K_{m,n}) = min 4 (min m n)             (m, n ≥ 2)
```
-/


namespace RomanDomination

open Finset

/-! ### Convex bipartite graphs -/

/-- A graph on `Fin m ⊕ Fin n` is *convex bipartite* when all its edges join the two
sides and, for every right vertex `b`, the set of left neighbours of `b` is an
interval in the natural order on `Fin m`. -/
def IsConvexBipartite {m n : ℕ} (G : SimpleGraph (Fin m ⊕ Fin n)) : Prop :=
  (∀ u v, G.Adj u v → (u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft)) ∧
  ∀ (b : Fin n) (i j k : Fin m), i ≤ j → j ≤ k →
    G.Adj (Sum.inl i) (Sum.inr b) → G.Adj (Sum.inl k) (Sum.inr b) →
    G.Adj (Sum.inl j) (Sum.inr b)


section CompleteBipartite

variable (m n : ℕ)

/-- The complete bipartite graph `K_{m,n}`. -/
abbrev K : SimpleGraph (Fin m ⊕ Fin n) := completeBipartiteGraph (Fin m) (Fin n)

instance : DecidableRel (K m n).Adj := fun u v =>
  decidable_of_iff ((u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft)) Iff.rfl

variable {m n}





variable (m n)


end CompleteBipartite

/-! ### Splitting weights over the two sides -/

section Weights

variable {m n : ℕ}







end Weights

/-! ### Roman dominating functions of `K_{m,n}`: structure -/

section KStructure

variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}







end KStructure

/-! ### The Roman domination number of `K_{m,n}` -/

section RomanValue

variable {m n : ℕ}

/-- `2` on the first left vertex, `1` on the other left vertices, `0` on the right. -/
def leftHeavy (m n : ℕ) : Fin m ⊕ Fin n → ℕ :=
  Sum.elim (fun i => if i.val = 0 then 2 else 1) (fun _ => 0)

/-- `2` on the first right vertex, `1` on the other right vertices, `0` on the left. -/
def rightHeavy (m n : ℕ) : Fin m ⊕ Fin n → ℕ :=
  Sum.elim (fun _ => 0) (fun j => if j.val = 0 then 2 else 1)

/-- `2` on the first vertex of each side, `0` elsewhere. -/
def cornerTwo (m n : ℕ) : Fin m ⊕ Fin n → ℕ :=
  Sum.elim (fun i => if i.val = 0 then 2 else 0) (fun j => if j.val = 0 then 2 else 0)

/-- `1` on every left vertex, `0` on the right. -/
def leftOnes (m n : ℕ) : Fin m ⊕ Fin n → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- `1` on every right vertex, `0` on the left. -/
def rightOnes (m n : ℕ) : Fin m ⊕ Fin n → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)









variable {f : Fin m ⊕ Fin n → ℕ}







end RomanValue

/-! ### The Italian domination number of `K_{m,n}` -/

section ItalianValue

variable {m n : ℕ}




variable {f : Fin m ⊕ Fin n → ℕ}






end ItalianValue

end RomanDomination


