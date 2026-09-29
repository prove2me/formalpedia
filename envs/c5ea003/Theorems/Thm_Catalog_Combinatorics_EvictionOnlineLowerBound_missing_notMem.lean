-- Prove2me | Theorems.Thm_Catalog_Combinatorics_EvictionOnlineLowerBound_missing_notMem
-- name    : Catalog.Combinatorics.EvictionOnlineLowerBound.missing_notMem
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:02:19.376844+00:00
-- url     : https://prove2.me/theorems/6c4f9507-d58a-4ada-9052-dbbe6a424ca1
-- title:
--   Missing notMem
-- statement:
--   Formal statement of `Catalog.Combinatorics.EvictionOnlineLowerBound.missing_notMem` from the Aether Catalog (Combinatorics). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Combinatorics.EvictionOnlineLowerBound.missing_notMem{B : ℕ} (hcard : Fintype.card α = B + 1) {C : Finset α}
--       (hC : C.card = B) : missing C ∉ C := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EvictionOnlineLowerBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EvictionOnlineLowerBound.lean#L191

-- Thm stub generated from Combinatorics/EvictionOnlineLowerBound.lean
import Mathlib
import Definitions.Def_Combinatorics_EvictionOnlineLowerBound

/-!
# Sequential eviction: every deterministic cheap-signal policy is a factor `B` from offline

Companion to `Catalog.Combinatorics.HybridEvictionAdditiveLaw`.  There the model
is *static* (one selection of `B` slots) and the conclusion is that the whole
additive-hybrid family sits below the oracle.  Here the model is *sequential*
(a request stream served out of a `B`-slot cache) and we prove the structural
reason a cheap online signal cannot close the gap: with `B + 1` live items an
adversary makes **any** deterministic eviction rule fault on *every* request,
while an offline schedule for the very same stream faults at most `⌈m / B⌉`
times.

Main results:

* `Serves` — the nondeterministic "some eviction schedule serves this stream
  with `k` faults" relation (demand paging: only a faulting request changes the
  cache, and it evicts exactly one resident item).
* `runCost` — the cost of the deterministic policy given by an eviction rule
  `A : Finset α → α → α`, and `serves_runCost`: that run *is* a legal schedule.
* `offline_cost_bound` — **offline upper bound**: on `B + 1` items, for every
  stream `σ` there is a schedule with `k` faults where `k * B < σ.length + B`
  (i.e. `k ≤ ⌈σ.length / B⌉`).
* `runCost_advSeq` — **online lower bound**: the adaptive adversary
  `advSeq A` forces the rule `A` to fault on all `m` requests.
* `online_lower_bound_factor_budget` — the two combined: for every rule `A`
  there is a stream of length `m` on which `A` faults `m` times while some
  offline schedule faults `k` times with `k * B < m + B`.
* `hybrid_online_lower_bound` — the specialisation to the NET-61 family: the
  rule "evict the resident item of least `a + λ·p`" is such a rule for *every*
  `λ`, so no probe weight — indeed no cheap score whatsoever — escapes the
  factor-`B` worst case.
-/

open Catalog.Combinatorics.EvictionOnlineLowerBound

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### Demand-paging schedules -/




/-! ### The offline upper bound on `B + 1` items -/

variable [Fintype α]



/-! ### The deterministic online policy and its adversary -/



variable [Nonempty α]

theorem Catalog.Combinatorics.EvictionOnlineLowerBound.missing_notMem{B : ℕ} (hcard : Fintype.card α = B + 1) {C : Finset α}
    (hC : C.card = B) : missing C ∉ C := by sorry
