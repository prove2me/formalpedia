-- Prove2me | solution 1 for Hashimoto.getLast_q_support
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T20:26:36.773984+00:00
-- url     : https://prove2.me/submissions/e6de64d4-c919-450a-ac92-e2afa3eded26

-- Sol generated from Algebra/NonBacktracking/CyclePositivity.lean
import Mathlib
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







open Hashimoto in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem solution{u v : V} (p : G.Walk u v) : p.support.getLast? = some v := by
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
      rw [SimpleGraph.Walk.support_cons]
      have hne : q.support ≠ [] := by simp [SimpleGraph.Walk.support_ne_nil]
      cases hq : q.support with
      | nil => exact absurd hq hne
      | cons x t =>
          rw [List.getLast?_cons_cons]
          rw [hq] at ih
          exact ih
