-- Prove2me | Definitions.Def_Geometry_RomanDomination_DoubleRoman
-- name    : Geometry_RomanDomination_DoubleRoman
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:50.995451+00:00
-- url     : https://prove2.me/theorems/068449de-2d30-459d-9b62-e8247b3ce315
-- title:
--   Aether Catalog definitions — Geometry_RomanDomination_DoubleRoman
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.RomanDomination.DoubleRoman`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/RomanDomination/DoubleRoman.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_Variants
/-
# The double Roman domination number of the complete bipartite graph

This file computes `γ_dR(K_{m,n})` exactly for all `m, n ≥ 1`.  Writing
`k = min m n`, the answer is

```
γ_dR(K_{m,n}) = 3   if k = 1,
              = 4   if k = 2,
              = 6   if k ≥ 3.
```

Note that this is *not* of the shape `min 6 (k + 2)`: the value jumps from `4`
to `6`, skipping `5`.

The lower bounds are obtained from the local conditions defining a double Roman
dominating function, applied to a `0`-labelled vertex on each side; the upper
bounds come from three explicit labellings (`3` on the unique left vertex,
`2` on both left vertices, and `3` on one vertex of each side).

Along the way we prove the general bound `3 ≤ γ_dR(G)` for every graph with at
least two vertices.
-/


namespace RomanDomination

open Finset

/-! ### General weight plumbing -/

section Plumbing

variable {α : Type*} [Fintype α] [DecidableEq α] {g : α → ℕ}




end Plumbing

/-! ### The general lower bound `3 ≤ γ_dR(G)` -/

section GeneralLower

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]






end GeneralLower

/-! ### Local consequences of the double Roman conditions on `K_{m,n}` -/

section KLocal

variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}













end KLocal

/-! ### Explicit double Roman dominating functions of `K_{m,n}` -/

section Constructions

variable {m n : ℕ}

/-- `3` on the unique left vertex, `0` on the right. -/
def leftThree (n : ℕ) : Fin 1 ⊕ Fin n → ℕ := Sum.elim (fun _ => 3) (fun _ => 0)

/-- `2` on every left vertex, `0` on the right. -/
def leftTwos (m n : ℕ) : Fin m ⊕ Fin n → ℕ := Sum.elim (fun _ => 2) (fun _ => 0)

/-- `3` on the first vertex of each side, `0` elsewhere. -/
def cornerThree (m n : ℕ) : Fin m ⊕ Fin n → ℕ :=
  Sum.elim (fun i => if i.val = 0 then 3 else 0) (fun j => if j.val = 0 then 3 else 0)







end Constructions

/-! ### Lower bounds for `K_{m,n}` -/

section KLower

variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}







end KLower

/-! ### Exact values -/

section Values

variable {m n : ℕ}








end Values

end RomanDomination


