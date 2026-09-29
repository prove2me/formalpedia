-- Prove2me | Theorems.Thm_Hashimoto_isChain_seam_iff_forall2_rotate
-- name    : Hashimoto.isChain_seam_iff_forall2_rotate
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:51:40.831216+00:00
-- url     : https://prove2.me/theorems/4694e3f9-aa72-4adf-b6f5-e134a8bc6852
-- title:
--   Cyclic chain criterion.
-- statement:
--   **Cyclic chain criterion.** A nonempty list is a chain for `R` which additionally
--   closes up (`R` relates its last entry to its first) exactly when it is `Forall₂`-related
--   to its own rotation by one.
--
--   ```lean
--   theorem Hashimoto.isChain_seam_iff_forall2_rotate{R : α → α → Prop} {l : List α} (hne : l ≠ []) :
--       (IsChain R l ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y) ↔ Forall₂ R l (l.rotate 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/VertexCycles.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/VertexCycles.lean#L79

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

theorem Hashimoto.isChain_seam_iff_forall2_rotate{R : α → α → Prop} {l : List α} (hne : l ≠ []) :
    (IsChain R l ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y) ↔ Forall₂ R l (l.rotate 1) := by sorry
