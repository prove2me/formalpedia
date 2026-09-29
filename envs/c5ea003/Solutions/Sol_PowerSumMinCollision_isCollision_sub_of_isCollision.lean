-- Prove2me | solution 1 for PowerSumMinCollision.isCollision_sub_of_isCollision
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:02:46.737994+00:00
-- url     : https://prove2.me/submissions/103c9ce8-8728-4cb8-8276-c17f164402a9

-- Sol generated from Probability/PowerSumMinimalCollision.lean
import Mathlib
import Definitions.Def_Probability_PowerSumMinimalCollision
import Definitions.Def_Probability_PowerSumSharpness
/-
# The minimal collision size `m(N, K)` of the finite moment problem

`Probability.PowerSumSharpness` and `Probability.PowerSumNewtonThreshold` establish the two
rigidity mechanisms for the finite moment problem on `{0, …, N}` (Vandermonde in the alphabet,
Newton in the size) together with sharpness witnesses.  This file turns those scattered bounds
into a *single numerical invariant* and computes it exactly in the cases that the previous
files bound from both sides.

For an alphabet bound `N` and an agreement order `K`, a **collision** is a pair of different
data sets `s ≠ t` of naturals bounded by `N` whose power sums agree for all orders `k ≤ K`.
Define

  `m(N, K) = minCollisionCard N K = sInf { card s | s, t is a collision }`.

Main results.

* `collisionSizes_eq_empty_of_le` / `minCollisionCard_eq_zero_iff` — collisions exist exactly
  when `K < N`, so `m(N, K) = 0` (the junk value of `sInf ∅`) precisely in the rigid regime.
* `lt_minCollisionCard` — the Prouhet–Tarry–Escott bound `K < m(N, K)` in the non-rigid regime.
* `minCollisionCard_antitone_alphabet` — `m(·, K)` is non-increasing in the alphabet: widening
  the alphabet can only make collisions cheaper.
* `minCollisionCard_critical` — **at the critical window `K = N − 1` the invariant is
  exactly `2^(N−1)`**, the largest value it can take.
* `minCollisionCard_one`, `minCollisionCard_two`, `minCollisionCard_three` — off the critical
  window the invariant collapses to the PTE floor `K + 1`: `m(N,1) = 2` for `N ≥ 2`,
  `m(N,2) = 3` for `N ≥ 4` and `m(N,3) = 4` for `N ≥ 11`.
* `minCollisionCard_strict_drop`, `minCollisionCard_two_table` — the exact drop profile at
  `K = 2`: `m(2,2) = 0`, `m(3,2) = 4`, `m(N,2) = 3` for all `N ≥ 4`.  This settles the
  `K = 2` case of sub-conjecture **S1** of `FUTURE_DIRECTIONS.md`.
* `isCollision_sub_of_isCollision`, `exists_disjoint_minimal_collision` — a collision of least
  size can always be taken *disjoint*: deleting the common part `s ∩ t` preserves agreement in
  every order and can only shrink the data sets.
-/

open PowerSumMinCollision

open Multiset

/-! ## 1. Collisions and the invariant `m(N, K)` -/




/-! ## 2. Existence and non-existence of collisions -/




/-! ## 3. General bounds on `m(N, K)` -/






/-! ## 4. The critical window `K = N - 1`: the invariant is exactly `2^(N-1)` -/



/-! ## 5. Off the critical window: the invariant collapses to the floor `K + 1` -/




/-! ## 6. The drop profile at `K = 2` -/



/-! ## 7. Minimal collisions are disjoint -/




open PowerSumMinCollision in
theorem solution{N K : ℕ} {s t : Multiset ℕ} (h : IsCollision N K s t) :
    IsCollision N K (s - t) (t - s) ∧ (s - t) ∩ (t - s) = 0 := by
  obtain ⟨hs, ht, hagree, hne⟩ := h
  have hsplit : ∀ (u v : Multiset ℕ) (k : ℕ),
      ((u - v).map (fun x => x ^ k)).sum + ((u ∩ v).map (fun x => x ^ k)).sum
        = (u.map (fun x => x ^ k)).sum := by
    intro u v k
    rw [← Multiset.sum_add, ← Multiset.map_add, Multiset.sub_add_inter]
  refine ⟨⟨fun x hx => hs x (Multiset.mem_of_le (Multiset.sub_le_self s t) hx),
      fun x hx => ht x (Multiset.mem_of_le (Multiset.sub_le_self t s) hx), ?_, ?_⟩, ?_⟩
  · intro k hk
    have e1 := hsplit s t k
    have e2 := hsplit t s k
    rw [Multiset.inter_comm s t] at e1
    have e3 := hagree k hk
    omega
  · intro hcon
    refine hne ?_
    calc s = s - t + s ∩ t := (Multiset.sub_add_inter s t).symm
      _ = t - s + t ∩ s := by rw [hcon, Multiset.inter_comm]
      _ = t := Multiset.sub_add_inter t s
  · ext x
    simp only [Multiset.count_inter, Multiset.count_sub, Multiset.count_zero]
    omega
