-- Prove2me | solution 1 for Combinatorics.DeploymentEntryCover.card_le_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:22:44.894147+00:00
-- url     : https://prove2.me/submissions/63e12372-0587-4920-8e0b-ffc5ff5d9ac4

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

/-- Two knees further than `δ` apart cannot share an entry. -/
theorem not_serves_both {δ b k l : ℕ} (hkl : k + δ < l) :
    ¬ (Serves δ b k ∧ Serves δ b l) := by
  rintro ⟨⟨_, h2⟩, ⟨h3, _⟩⟩
  omega


/-! ## The greedy upper bound -/




/-! ## Packing meets covering -/






/-! ## The measured three-domain table -/









open Combinatorics.DeploymentEntryCover in
theorem solution{δ : ℕ} {K S E : Finset ℕ} (hSK : S ⊆ K)
    (hsep : ∀ k ∈ S, ∀ l ∈ S, k < l → k + δ < l) (hE : IsEntrySet δ K E) :
    S.card ≤ E.card := by
  classical
  choose f hf hfs using fun k (hk : k ∈ S) => hE k (hSK hk)
  refine Finset.card_le_card_of_injOn (fun k => if hk : k ∈ S then f k hk else 0) ?_ ?_
  · intro k hk
    have hk' : k ∈ S := hk
    simp only [dif_pos hk']
    exact hf k hk'
  · intro k hk l hl hkl
    have hk : k ∈ S := hk
    have hl : l ∈ S := hl
    simp only [dif_pos hk, dif_pos hl] at hkl
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact not_serves_both (hsep k hk l hl h) ⟨hfs k hk, hkl ▸ hfs l hl⟩
    · exact not_serves_both (hsep l hl k hk h) ⟨hfs l hl, hkl ▸ hfs k hk⟩
