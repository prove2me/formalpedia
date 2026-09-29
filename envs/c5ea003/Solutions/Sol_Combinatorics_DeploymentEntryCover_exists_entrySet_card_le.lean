-- Prove2me | solution 1 for Combinatorics.DeploymentEntryCover.exists_entrySet_card_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:22:45.545319+00:00
-- url     : https://prove2.me/submissions/3b2140d6-caf8-4492-8e76-5bb77b75d27b

-- Sol generated from Combinatorics/DeploymentEntryCover.lean
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


theorem greedyEntries_card_le (δ b m : ℕ) : (greedyEntries δ b m).card ≤ m := by
  unfold greedyEntries
  exact le_trans (card_image_le) (by simp)


/-! ## Packing meets covering -/






/-! ## The measured three-domain table -/









open Combinatorics.DeploymentEntryCover in
theorem solution{δ a b : ℕ} {K : Finset ℕ}
    (hK : ∀ k ∈ K, a ≤ k ∧ k ≤ b) :
    ∃ E : Finset ℕ, IsEntrySet δ K E ∧ E.card ≤ (b - a) / (δ + 1) + 1 := by
  refine ⟨greedyEntries δ b ((b - a) / (δ + 1) + 1), ?_, greedyEntries_card_le _ _ _⟩
  intro k hk
  obtain ⟨hak, hkb⟩ := hK k hk
  set y := b - k with hy
  have hyk : k + y = b := by omega
  have hyba : y ≤ b - a := by omega
  have hdm : y % (δ + 1) + (δ + 1) * (y / (δ + 1)) = y := Nat.mod_add_div y (δ + 1)
  have hmod : y % (δ + 1) < δ + 1 := Nat.mod_lt _ (Nat.succ_pos δ)
  refine ⟨b - (δ + 1) * (y / (δ + 1)), ?_, ?_, ?_⟩
  · unfold greedyEntries
    refine mem_image.mpr ⟨y / (δ + 1), mem_range.mpr ?_, rfl⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (c := δ + 1) hyba)
  · generalize (δ + 1) * (y / (δ + 1)) = q at hdm ⊢
    omega
  · generalize (δ + 1) * (y / (δ + 1)) = q at hdm ⊢
    omega
