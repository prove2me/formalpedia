-- Prove2me | Definitions.Def_Bridges_TuranPartiteSharp
-- name    : Bridges_TuranPartiteSharp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:25.770075+00:00
-- url     : https://prove2.me/theorems/73a63eb5-518a-4677-a7cb-74ca897702dd
-- title:
--   Aether Catalog definitions — Bridges_TuranPartiteSharp
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TuranPartiteSharp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TuranPartiteSharp.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_TuranExplicitCount
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Turán graph is optimal among all `r`-colourable graphs — sharply, and by hand

`Catalog/Bridges/TuranSharpNonDivisible.lean` computes the exact number of edges of the Turán
graph for every `n` and every `r ≥ 1`.  This file proves, from scratch and with no appeal to
Mathlib's structural Turán theorem, that **no** `r`-colourable graph on `n` vertices can beat it.

The argument has two independent halves.

* An *integer* convexity step (`sum_sq_ge_balanced`): among all ways of writing `n` as a sum of
  `r` natural numbers, the sum of squares is minimized by the balanced split.  The proof is the
  tangent-line trick over `ℤ`: `(c − q)(c − q − 1) ≥ 0` for every integer `c`, i.e.
  `c² ≥ (2q+1)c − q(q+1)`, summed over the parts.  This is *sharp for integers*, unlike
  Cauchy–Schwarz, which would only give `n²/r`.
* A *counting* step (`two_mul_card_edgeFinset_add_sum_sq_le`): for a proper `r`-colouring the
  degree of a vertex misses its whole colour class, so `2·#edges + ∑_i c_i² ≤ n²`.

Main results:

* `sum_sq_ge_balanced` — `r·(n/r)² + (n % r)·(2·(n/r) + 1) ≤ ∑_i c_i²` for all `c` with
  `∑_i c_i = n`.
* `two_mul_card_edgeFinset_add_sum_sq_le` — the colour-class degree count.
* `turan_bound_of_colourable` — every `r`-colourable graph on `n` vertices satisfies
  `2·r·#edges + (n % r)·(r − n % r) ≤ (r − 1)·n²`, the sharp integer form of
  `#edges ≤ (1 − 1/r)n²/2`.
* `card_edgeFinset_le_turanGraph_of_colourable` — every `r`-colourable graph on `Fin n` has at
  most as many edges as `turanGraph n r`, with equality for the Turán graph itself
  (`card_edgeFinset_turanGraph_isGreatest_colourable`).
-/


open Finset SimpleGraph
open scoped BigOperators

namespace TuranPartiteSharp

open TuranExplicitCount

/-! ## The integer convexity step -/



/-! ## The counting step -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The size of the colour class `i` of the colouring `f`. -/
def colourClassCard {r : ℕ} (f : V → Fin r) (i : Fin r) : ℕ :=
  #((univ : Finset V).filter (fun v => f v = i))





/-! ## The sharp bound for `r`-colourable graphs -/




end TuranPartiteSharp


