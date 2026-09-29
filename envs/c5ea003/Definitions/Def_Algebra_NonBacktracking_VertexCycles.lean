-- Prove2me | Definitions.Def_Algebra_NonBacktracking_VertexCycles
-- name    : Algebra_NonBacktracking_VertexCycles
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:26:44.978842+00:00
-- url     : https://prove2.me/theorems/dd7bbcdf-c844-4efe-b878-ecd9afeed1fb
-- title:
--   Aether Catalog definitions — Algebra_NonBacktracking_VertexCycles
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.NonBacktracking.VertexCycles`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/NonBacktracking/VertexCycles.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace

/-!
# The vertex form of the non-backtracking trace formula

`Hashimoto.trace_hashimoto_pow` counts rooted closed non-backtracking walks as lists of
*darts*.  Classically one prefers the *vertex* description: a rooted closed
non-backtracking walk of length `n` is a cyclic word `u₀ u₁ … u_{n-1}` of vertices with

* `uᵢ` adjacent to `u_{i+1}` for all `i` **cyclically**, and
* `u_{i+2} ≠ uᵢ` for all `i` **cyclically** (no immediate backtracking, including across
  the seam).

Cyclic conditions are expressed with `List.rotate`: "`∀ i, R uᵢ u_{i+1 mod n}`" is exactly
`List.Forall₂ R u (u.rotate 1)`.

## Main results

* `Hashimoto.isChain_seam_iff_forall₂_rotate` — a list is a chain *and* closes up under
  the relation iff it is `Forall₂`-related to its own rotation. This converts the linear
  (chain) description of closed walks into the genuinely cyclic one.
* `Hashimoto.mem_cyclicNBVertexSeqs` — the vertex description above really describes the
  image of the dart cycles under `d ↦ d.fst`.
* `Hashimoto.trace_hashimoto_pow_eq_card_cyclicNBVertexSeqs` —
  `trace (B ^ n) = #{cyclically non-backtracking closed vertex words of length n}`
  for `n ≥ 1`.
-/

open Finset RelWalkCount SimpleGraph List

namespace Hashimoto

/-! ## List lemmas -/

section ListLemmas

variable {α β γ γ' : Type*}






end ListLemmas

/-! ## Cyclic dart words -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable {G}



variable (G)

/-! ## Cyclic vertex words -/

/-- The finset of **cyclically non-backtracking closed vertex words** of length `n`: the
vertex trace of the dart cycles counted by `trace (B ^ n)`. -/
def cyclicNBVertexSeqs (n : ℕ) : Finset (List V) :=
  (nbCycles G n).image (List.map fun d => d.toProd.1)

variable {G}




variable (G)


end Hashimoto


