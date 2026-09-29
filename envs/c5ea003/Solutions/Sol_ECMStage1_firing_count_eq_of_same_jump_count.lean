-- Prove2me | solution 1 for ECMStage1.firing_count_eq_of_same_jump_count
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:46:17.915033+00:00
-- url     : https://prove2.me/submissions/34199f7c-a23b-4c54-9157-a1c11f3a1ea9

-- Sol generated from Shared/ECMStage1FlatRun.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FiringRate
import Definitions.Def_Shared_ECMStage1FlatRun
import Definitions.Def_Shared_ECMStage1OrderCompletion
import Theorems.Thm_ECMStage1_gcd_stage1_flat
import Theorems.Thm_ECMStage1_jumpSet_eq_primeFactors_filter

/-!
# A long flat run in the schedule: the pigeonhole behind the observed non-uniformity

The staircase results of `Catalog.Shared.ECMStage1FiringRate` say that the cumulative
firing count `C ↦ gcd(m, k(B,C))` jumps exactly at the prime divisors of the order below
the bound, hence at most `ω(m)` times.  Here we draw the consequence that the
experimental KS analysis was really detecting: since the schedule has `π(B)` steps and
the staircase has at most `ω(m)` jumps, **some block of the schedule of length at least
`π(B) / (ω(m)+1)` does nothing at all**.

* `firing_count_eq_of_same_jump_count` — two schedule primes with the same number of
  jumps below them carry the same firing count.
* `exists_flat_run` — a set of at least `π(B) / (ω(m)+1)` schedule primes on which the
  firing count is constant.
* `exists_flat_run_half` — the readable corollary: for an order with at most one prime
  divisor below the bound, at least half the schedule is inert.

The uniform comparison distribution increases at every one of the `π(B)` steps, so a flat
run of that length is exactly the obstruction to uniformity that the KS statistic picks
up; the quantitative sup-distance version is conjecture 1 of `FUTURE_DIRECTIONS.md`.
-/

open ECMStage1

open Finset







open ECMStage1 in
theorem solution{m B C C' : ℕ} (hm : m ≠ 0) (hB : B ≠ 0)
    (hC' : C' ≤ B) (hle : C ≤ C')
    (hcount : ((jumpSet m B).filter (fun q => q ≤ C)).card
      = ((jumpSet m B).filter (fun q => q ≤ C')).card) :
    Nat.gcd m (stage1 B C) = Nat.gcd m (stage1 B C') := by
  have hsub : (jumpSet m B).filter (fun q => q ≤ C) ⊆ (jumpSet m B).filter (fun q => q ≤ C') := by
    intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.trans hle⟩
  have heq : (jumpSet m B).filter (fun q => q ≤ C) = (jumpSet m B).filter (fun q => q ≤ C') :=
    Finset.eq_of_subset_of_card_le hsub hcount.ge
  refine gcd_stage1_flat hm hB hle ?_
  intro q hq hqC'
  by_contra hqC
  push_neg at hqC
  have hqB : q ≤ B := hqC'.trans hC'
  have hqjump : q ∈ jumpSet m B := by
    rw [jumpSet_eq_primeFactors_filter hm hB]
    exact Finset.mem_filter.mpr ⟨hq, hqB⟩
  have h1 : q ∈ (jumpSet m B).filter (fun r => r ≤ C') :=
    Finset.mem_filter.mpr ⟨hqjump, hqC'⟩
  rw [← heq] at h1
  exact absurd (Finset.mem_filter.mp h1).2 (by omega)
