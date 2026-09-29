-- Prove2me | Definitions.Def_Novelty_ProbeKneeBridge
-- name    : Novelty_ProbeKneeBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:04.658387+00:00
-- url     : https://prove2.me/theorems/24269302-c81a-4376-b6fb-a53ec741a7d0
-- title:
--   Aether Catalog definitions — Novelty_ProbeKneeBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ProbeKneeBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ProbeKneeBridge.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ProbeHybridStability

/-!
# The knee is a lower bound for *every* eviction policy (NET-67 ⋈ NET-69)

`Novelty.AttentionRetentionKnee` (round 21, NET-67) studies the knee
`knee p τ = sInf {k | τ ≤ ∑_{i<k} p i}` of a *sorted* attention profile: the
number of keys the top-`k` policy needs in order to reach the drift-assert
threshold `τ`.  `Novelty.ProbeRetentionLimits` (round 22, NET-69) studies
arbitrary budget-`B` selection rules driven by a score.  This file joins them.

The bridge is the observation that, for a sorted profile, the **prefix is a top
set** in the sense of NET-69 (`isTopSet_prefixSel`).  Everything follows:

* `retained_le_retained_prefix` — no budget-`B` policy, however clever, retains
  more mass than the prefix of length `B`.  The NET-67 retention curve is thus
  not merely the curve of one heuristic; it is the *envelope* of all policies.
* `retained_lt_of_card_lt_knee` — below the knee **every** policy misses the
  threshold.  The knee is therefore a hard budget floor, not an artefact of
  top-`k` eviction: reporting `12/16` keys for code (NET-68) is reporting a
  quantity no scoring rule can beat.
* `knee_le_of_reaches` — the contrapositive, in the form used experimentally:
  an arm that passes the drift assert at budget `B` certifies `knee ≤ B`.
* `probe_at_knee_budget` — the NET-69 arms re-enter: a score with `L∞` error `ε`
  run at any budget `B ≥ knee p τ` still retains at least `τ - 2Bε`.  Combined
  with the sharpness instance `sup_transfer_bound_is_sharp`, this is the exact
  price of content-blindness: a weak probe costs mass at most linearly in the
  budget and its error, and that linear rate is attained.
-/

namespace Catalog.Novelty.ProbeKneeBridge

open Finset Catalog.Novelty.ProbeRetentionLimits

variable {n k B : ℕ} {p : ℕ → ℝ} {tau : ℝ}

/-- The importance vector that a sorted profile `p` induces on a context of `n`
keys. -/
def keyMass (p : ℕ → ℝ) (n : ℕ) : Fin n → ℝ := fun i => p (i : ℕ)

/-- The prefix selection: the `k` best-ranked keys of an `n`-key context. -/
def prefixSel (n k : ℕ) (h : k ≤ n) : Finset (Fin n) :=
  (Finset.range k).attachFin fun _ hm => lt_of_lt_of_le (Finset.mem_range.mp hm) h









end Catalog.Novelty.ProbeKneeBridge


