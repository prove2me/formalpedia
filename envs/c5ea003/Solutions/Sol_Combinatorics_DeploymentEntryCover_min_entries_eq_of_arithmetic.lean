-- Prove2me | solution 1 for Combinatorics.DeploymentEntryCover.min_entries_eq_of_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:27:00.034984+00:00
-- url     : https://prove2.me/submissions/60fdd655-bcf3-4fe4-82dc-c1313ecb9060

-- Sol generated from Combinatorics/DeploymentEntryCover.lean
import Mathlib
import Definitions.Def_Combinatorics_DeploymentEntryCover
import Definitions.Def_Combinatorics_MathReadsAsProse
import Theorems.Thm_Combinatorics_DeploymentEntryCover_card_le_of_separated
import Theorems.Thm_Combinatorics_DeploymentEntryCover_exists_entrySet_card_le

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




/-! ## Packing meets covering -/


theorem apKnees_card (δ a m : ℕ) : (apKnees δ a m).card = m := by
  unfold apKnees
  have hinj : Function.Injective fun i => a + (δ + 1) * i := by
    intro x y hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos δ) (Nat.add_left_cancel hxy)
  rw [card_image_of_injective _ hinj, card_range]

theorem apKnees_separated (δ a m : ℕ) :
    ∀ k ∈ apKnees δ a m, ∀ l ∈ apKnees δ a m, k < l → k + δ < l := by
  intro k hk l hl hkl
  unfold apKnees at hk hl
  obtain ⟨i, _, rfl⟩ := mem_image.mp hk
  obtain ⟨j, _, rfl⟩ := mem_image.mp hl
  have hlt : (δ + 1) * i < (δ + 1) * j := Nat.lt_of_add_lt_add_left hkl
  have hij : i < j := Nat.lt_of_mul_lt_mul_left hlt
  have hstep : (δ + 1) * (i + 1) ≤ (δ + 1) * j := Nat.mul_le_mul_left _ hij
  have hexp : (δ + 1) * (i + 1) = (δ + 1) * i + δ + 1 := by ring
  rw [hexp] at hstep
  linarith

theorem apKnees_bounds {δ a m : ℕ} :
    ∀ k ∈ apKnees δ a m, a ≤ k ∧ k ≤ a + (δ + 1) * (m - 1) := by
  intro k hk
  unfold apKnees at hk
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
  have hi' : i ≤ m - 1 := by have := mem_range.mp hi; omega
  refine ⟨by omega, ?_⟩
  have := Nat.mul_le_mul_left (δ + 1) hi'
  linarith


/-! ## The measured three-domain table -/









open Combinatorics.DeploymentEntryCover in
theorem solution(δ a m : ℕ) (hm : 0 < m) :
    (∃ E : Finset ℕ, IsEntrySet δ (apKnees δ a m) E ∧ E.card ≤ m) ∧
      (∀ E : Finset ℕ, IsEntrySet δ (apKnees δ a m) E → m ≤ E.card) := by
  constructor
  · obtain ⟨E, hE, hcard⟩ :=
      exists_entrySet_card_le (δ := δ) (a := a) (b := a + (δ + 1) * (m - 1))
        (K := apKnees δ a m) apKnees_bounds
    refine ⟨E, hE, le_trans hcard ?_⟩
    have hsub : a + (δ + 1) * (m - 1) - a = (δ + 1) * (m - 1) := by omega
    have hdiv : (a + (δ + 1) * (m - 1) - a) / (δ + 1) = m - 1 := by
      rw [hsub, Nat.mul_div_cancel_left _ (by omega : 0 < δ + 1)]
    omega
  · intro E hE
    have := card_le_of_separated (K := apKnees δ a m) (S := apKnees δ a m)
      (Subset.refl _) (apKnees_separated δ a m) hE
    rwa [apKnees_card] at this
