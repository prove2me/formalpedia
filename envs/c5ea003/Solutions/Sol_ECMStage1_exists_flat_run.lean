-- Prove2me | solution 1 for ECMStage1.exists_flat_run
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:47:47.567002+00:00
-- url     : https://prove2.me/submissions/3eacc06c-41d5-4daf-9244-cb8113e5be38

-- Sol generated from Shared/ECMStage1FlatRun.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FiringRate
import Definitions.Def_Shared_ECMStage1FlatRun
import Definitions.Def_Shared_ECMStage1OrderCompletion
import Theorems.Thm_ECMStage1_card_jumpSet_le
import Theorems.Thm_ECMStage1_firing_count_eq_of_same_jump_count

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


theorem card_schedule (B : ℕ) : (schedule B).card = primeCount B := rfl





open ECMStage1 in
theorem solution{m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) :
    ∃ S ⊆ schedule B, primeCount B / (m.primeFactors.card + 1) ≤ S.card ∧
      ∀ C ∈ S, ∀ C' ∈ S, Nat.gcd m (stage1 B C) = Nat.gcd m (stage1 B C') := by
  classical
  set j := m.primeFactors.card with hj
  set f : ℕ → ℕ := fun C => ((jumpSet m B).filter (fun q => q ≤ C)).card with hf
  have hmaps : ∀ C ∈ schedule B, f C ∈ Finset.range (j + 1) := by
    intro C _
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    calc ((jumpSet m B).filter (fun q => q ≤ C)).card ≤ (jumpSet m B).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ j := (card_jumpSet_le hm hB).1
  have hne : (Finset.range (j + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  have hcard : (Finset.range (j + 1)).card * (primeCount B / (j + 1)) ≤ (schedule B).card := by
    rw [Finset.card_range, card_schedule]
    calc (j + 1) * (primeCount B / (j + 1))
        = (primeCount B / (j + 1)) * (j + 1) := Nat.mul_comm _ _
      _ ≤ primeCount B := Nat.div_mul_le_self _ _
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps hne hcard
  refine ⟨(schedule B).filter (fun C => f C = y), Finset.filter_subset _ _, hy, ?_⟩
  intro C hC C' hC'
  simp only [Finset.mem_filter, schedule, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff] at hC hC'
  obtain ⟨⟨hCB, -⟩, hCy⟩ := hC
  obtain ⟨⟨hCB', -⟩, hCy'⟩ := hC'
  rcases Nat.le_total C C' with hle | hle
  · exact firing_count_eq_of_same_jump_count hm hB hCB' hle (hCy.trans hCy'.symm)
  · exact (firing_count_eq_of_same_jump_count hm hB hCB hle (hCy'.trans hCy.symm)).symm
