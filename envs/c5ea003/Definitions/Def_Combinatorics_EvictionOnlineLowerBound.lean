-- Prove2me | Definitions.Def_Combinatorics_EvictionOnlineLowerBound
-- name    : Combinatorics_EvictionOnlineLowerBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:43:26.284557+00:00
-- url     : https://prove2.me/theorems/3b9e4137-5fb7-4823-8aa5-c4fcaeac2b8c
-- title:
--   Aether Catalog definitions — Combinatorics_EvictionOnlineLowerBound
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EvictionOnlineLowerBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EvictionOnlineLowerBound.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.Combinatorics.EvictionOnlineLowerBound

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### Demand-paging schedules -/

/-- `Serves C σ k`: starting from cache `C`, the request stream `σ` can be
served with exactly `k` faults by *some* eviction schedule.  A hit leaves the
cache unchanged; a fault brings the requested item in and evicts one resident
item. -/
inductive Serves : Finset α → List α → ℕ → Prop
  | nil (C : Finset α) : Serves C [] 0
  | hit {C : Finset α} {r : α} {rest : List α} {k : ℕ} (h : r ∈ C)
      (hs : Serves C rest k) : Serves C (r :: rest) k
  | miss {C : Finset α} {r e : α} {rest : List α} {k : ℕ} (hr : r ∉ C) (he : e ∈ C)
      (hs : Serves (insert r (C.erase e)) rest k) : Serves C (r :: rest) (k + 1)



/-! ### The offline upper bound on `B + 1` items -/

variable [Fintype α]



/-! ### The deterministic online policy and its adversary -/

/-- The cost of the deterministic policy that, on a fault, evicts `A C r`. -/
def runCost (A : Finset α → α → α) : List α → Finset α → ℕ
  | [], _ => 0
  | r :: rest, C =>
      if r ∈ C then runCost A rest C
      else runCost A rest (insert r (C.erase (A C r))) + 1


variable [Nonempty α]

/-- The item currently outside the cache (well defined as soon as the cache is
not everything). -/
noncomputable def missing (C : Finset α) : α :=
  if h : (Finset.univ \ C).Nonempty then h.choose else Classical.arbitrary α


/-- The adaptive adversary: always request the one item the policy just threw
away. -/
noncomputable def advSeq (A : Finset α → α → α) : ℕ → Finset α → List α
  | 0, _ => []
  | m + 1, C =>
      missing C :: advSeq A m (insert (missing C) (C.erase (A C (missing C))))



/-! ### The factor-`B` separation -/


/-! ### The NET-61 family is one of these rules -/

/-- The eviction rule of the additive hybrid: evict the resident slot of least
`a + λ·p`. -/
noncomputable def hybridEvictor (a p : α → ℝ) (lam : ℝ) : Finset α → α → α :=
  fun C _ =>
    if h : C.Nonempty then
      (Finset.exists_min_image C (fun i => a i + lam * p i) h).choose
    else Classical.arbitrary α



/-! ### Non-vacuity: the separation is realised on `Fin (B+1)` -/


end Catalog.Combinatorics.EvictionOnlineLowerBound


