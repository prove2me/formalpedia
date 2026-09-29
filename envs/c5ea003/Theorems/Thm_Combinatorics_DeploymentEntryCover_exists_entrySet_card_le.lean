-- Prove2me | Theorems.Thm_Combinatorics_DeploymentEntryCover_exists_entrySet_card_le
-- name    : Combinatorics.DeploymentEntryCover.exists_entrySet_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:04:23.753725+00:00
-- url     : https://prove2.me/theorems/4422ef22-9e39-486c-b6e1-b2663ef8db14
-- title:
--   Greedy covering bound.
-- statement:
--   **Greedy covering bound.**  Any knee set inside `[a, b]` is served by
--   `(b - a) / (δ + 1) + 1` entries.
--
--   ```lean
--   theorem Combinatorics.DeploymentEntryCover.exists_entrySet_card_le{δ a b : ℕ} {K : Finset ℕ}
--       (hK : ∀ k ∈ K, a ≤ k ∧ k ≤ b) :
--       ∃ E : Finset ℕ, IsEntrySet δ K E ∧ E.card ≤ (b - a) / (δ + 1) + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DeploymentEntryCover.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DeploymentEntryCover.lean#L111

-- Thm stub generated from Combinatorics/DeploymentEntryCover.lean
import Mathlib
import Definitions.Def_Combinatorics_DeploymentEntryCover
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

open Combinatorics.DeploymentEntryCover

open Finset




/-! ## One entry -/


/-! ## The packing lower bound -/



/-! ## The greedy upper bound -/

theorem Combinatorics.DeploymentEntryCover.exists_entrySet_card_le{δ a b : ℕ} {K : Finset ℕ}
    (hK : ∀ k ∈ K, a ≤ k ∧ k ≤ b) :
    ∃ E : Finset ℕ, IsEntrySet δ K E ∧ E.card ≤ (b - a) / (δ + 1) + 1 := by sorry
