-- Prove2me | Theorems.Thm_Hashimoto_dartList_ext
-- name    : Hashimoto.dartList_ext
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:35:06.591096+00:00
-- url     : https://prove2.me/theorems/45baf210-ad6d-4816-b3ea-ff1a985edd35
-- title:
--   A list of darts is determined by the lists of its tails and of its heads.
-- statement:
--   A list of darts is determined by the lists of its tails and of its heads.
--
--   ```lean
--   theorem Hashimoto.dartList_ext: ∀ {c c' : List G.Dart},
--       c.map (fun d => d.toProd.1) = c'.map (fun d => d.toProd.1) →
--       c.map (fun d => d.toProd.2) = c'.map (fun d => d.toProd.2) → c = c' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/VertexCycles.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/VertexCycles.lean#L118

-- Thm stub generated from Algebra/NonBacktracking/VertexCycles.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_VertexCycles

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

open Hashimoto

/-! ## List lemmas -/


variable {α β γ γ' : Type*}







/-! ## Cyclic dart words -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable {G}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

theorem Hashimoto.dartList_ext: ∀ {c c' : List G.Dart},
    c.map (fun d => d.toProd.1) = c'.map (fun d => d.toProd.1) →
    c.map (fun d => d.toProd.2) = c'.map (fun d => d.toProd.2) → c = c' := by sorry
