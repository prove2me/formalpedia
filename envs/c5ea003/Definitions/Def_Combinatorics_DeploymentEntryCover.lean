-- Prove2me | Definitions.Def_Combinatorics_DeploymentEntryCover
-- name    : Combinatorics_DeploymentEntryCover
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:32:11.172866+00:00
-- url     : https://prove2.me/theorems/b3c56542-0f9c-4ccd-8752-faca5a944334
-- title:
--   Aether Catalog definitions — Combinatorics_DeploymentEntryCover
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.DeploymentEntryCover`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/DeploymentEntryCover.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_MathReadsAsProse

/-!
# Deployment entries as an interval point-cover (NET-70, cycle 2)

NET-70 ends with an operational claim: *"prose + math workloads share one entry;
only code shifts"*.  This file makes that claim a theorem of extremal
combinatorics and then asks — and answers — the sharper question it raises:

> given the three-domain knee set `{prose ↦ 16, code ↦ 12, math ↦ 16}` and an
> over-provisioning tolerance `δ` (how many keys of waste a deployment is
> willing to pay on the cheapest domain), how many distinct cache-size entries
> does a fleet actually need?

A single served entry `b` for a domain of knee `k` must satisfy `k ≤ b` (else
quality falls below the gate) and `b ≤ k + δ` (else the waste budget is blown).
So an entry is a *point* and a domain is the *interval* `[k, k+δ]`: the number
of entries is the minimum number of points meeting a family of equal-length
integer intervals.

Results:

* `single_entry_iff` — one entry suffices **iff** the knee spread is at most
  `δ`.  This is the exact criterion behind the NET-70 deployment sentence.
* `card_le_of_separated` — a **packing lower bound**: `δ`-separated knees force
  distinct entries (pigeonhole via an injection into any entry set).
* `exists_entrySet_card_le` — a **greedy upper bound**: knees inside `[a, b]`
  are always served by the arithmetic progression `a, a+δ+1, …`, of size
  `(b-a)/(δ+1) + 1`.
* `min_entries_eq_of_arithmetic` — the two bounds **meet** on the extremal
  configuration: for an arithmetic progression of knees with common difference
  `δ+1` the minimum number of entries is exactly its length.  A genuine min–max
  (packing = covering) duality for this deployment problem.
* `net70_three_domains_one_entry`, `net70_three_domains_need_two` — the measured
  table: with `δ ≥ 4` the whole three-domain fleet collapses to the *single*
  entry `16`; with `δ ≤ 3` it provably needs two.  The NET-70 sentence is
  therefore the `δ ≤ 3` regime, and `δ = 4` — exactly one scale increment
  (NET-67) — is the point where code rejoins prose and math.
-/

namespace Combinatorics.DeploymentEntryCover

open Finset

/-- A cache-size entry `b` **serves** a domain of knee `k` at waste tolerance
`δ` when it is large enough to clear the gate and not wasteful by more than
`δ`. -/
def Serves (δ b k : ℕ) : Prop := k ≤ b ∧ b ≤ k + δ

instance (δ b k : ℕ) : Decidable (Serves δ b k) := by unfold Serves; infer_instance

/-- `E` is a valid **entry set** for the knee set `K`. -/
def IsEntrySet (δ : ℕ) (K E : Finset ℕ) : Prop := ∀ k ∈ K, ∃ b ∈ E, Serves δ b k

/-! ## One entry -/


/-! ## The packing lower bound -/



/-! ## The greedy upper bound -/

/-- The greedy entry set on `[a, b]`: the arithmetic progression of step
`δ + 1` counted **down** from the top of the knee range (an entry must be at
least as large as the knee it serves, so the progression is anchored above). -/
def greedyEntries (δ b m : ℕ) : Finset ℕ := (range m).image fun i => b - (δ + 1) * i



/-! ## Packing meets covering -/

/-- The extremal knee configuration: `m` knees spaced exactly `δ + 1` apart. -/
def apKnees (δ a m : ℕ) : Finset ℕ := (range m).image fun i => a + (δ + 1) * i





/-! ## The measured three-domain table -/

/-- The NET-70 knee set at ctx 512: `code ↦ 12`, `prose ↦ 16`, `math ↦ 16`. -/
def net70Knees : Finset ℕ := {12, 16}







end Combinatorics.DeploymentEntryCover


