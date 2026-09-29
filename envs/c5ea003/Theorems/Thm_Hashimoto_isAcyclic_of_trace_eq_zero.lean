-- Prove2me | Theorems.Thm_Hashimoto_isAcyclic_of_trace_eq_zero
-- name    : Hashimoto.isAcyclic_of_trace_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:35:34.00858+00:00
-- url     : https://prove2.me/theorems/6573ebf3-0275-458d-823f-702c1d7bab79
-- title:
--   Acyclicity detector.
-- statement:
--   **Acyclicity detector.** If every positive power of the Hashimoto matrix has zero
--   trace — equivalently, `G` has no rooted closed non-backtracking walk of positive
--   length — then `G` is acyclic.
--
--   ```lean
--   theorem Hashimoto.isAcyclic_of_trace_eq_zero    (h : ∀ n : ℕ, 1 ≤ n → (hashimoto G ^ n).trace = 0) : G.IsAcyclic := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/CyclePositivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/CyclePositivity.lean#L108

-- Thm stub generated from Algebra/NonBacktracking/CyclePositivity.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_VertexCycles

/-!
# Cycles make the non-backtracking trace positive

The trace formula turns a purely graph-theoretic statement — "`G` contains a cycle" —
into an algebraic one about the Hashimoto matrix `B`.

## Main results

* `Hashimoto.one_le_trace_of_nodup_cyclic` — a closed cyclically adjacent vertex word of
  length at least three with distinct letters contributes a rooted closed
  non-backtracking walk, so `1 ≤ trace (B ^ m)`.
* `Hashimoto.one_le_trace_of_isCycle` — every cycle of length `m` in `G` forces
  `1 ≤ trace (B ^ m)`.
* `Hashimoto.isAcyclic_of_trace_eq_zero` — conversely, if all traces `trace (B ^ n)`
  vanish for `n ≥ 1` then `G` is acyclic. Together with `Hashimoto.trace_hashimoto_pow`
  this says: the non-backtracking trace sequence detects the presence of cycles.
-/

open Finset SimpleGraph List

open Hashimoto

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Distinct letters give no backtracking -/



/-! ## From cycles in the graph -/

theorem Hashimoto.isAcyclic_of_trace_eq_zero    (h : ∀ n : ℕ, 1 ≤ n → (hashimoto G ^ n).trace = 0) : G.IsAcyclic := by sorry
