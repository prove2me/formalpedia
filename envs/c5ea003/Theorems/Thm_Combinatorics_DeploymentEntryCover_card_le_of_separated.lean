-- Prove2me | Theorems.Thm_Combinatorics_DeploymentEntryCover_card_le_of_separated
-- name    : Combinatorics.DeploymentEntryCover.card_le_of_separated
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:04:17.6128+00:00
-- url     : https://prove2.me/theorems/1ac3e2d9-959f-4c34-95a9-a896c56e5c09
-- title:
--   Packing bound.
-- statement:
--   **Packing bound.**  If `S ⊆ K` is pairwise `δ`-separated, then every entry
--   set for `K` has at least `#S` entries: distinct separated knees are served by
--   distinct entries.
--
--   ```lean
--   theorem Combinatorics.DeploymentEntryCover.card_le_of_separated{δ : ℕ} {K S E : Finset ℕ} (hSK : S ⊆ K)
--       (hsep : ∀ k ∈ S, ∀ l ∈ S, k < l → k + δ < l) (hE : IsEntrySet δ K E) :
--       S.card ≤ E.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DeploymentEntryCover.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DeploymentEntryCover.lean#L78

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

theorem Combinatorics.DeploymentEntryCover.card_le_of_separated{δ : ℕ} {K S E : Finset ℕ} (hSK : S ⊆ K)
    (hsep : ∀ k ∈ S, ∀ l ∈ S, k < l → k + δ < l) (hE : IsEntrySet δ K E) :
    S.card ≤ E.card := by sorry
