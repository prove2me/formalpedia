-- Prove2me | solution 1 for Catalog.Tropical.KneeMedian.card_filter_add_card_filter_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:41:26.867216+00:00
-- url     : https://prove2.me/submissions/bffd33ca-c881-4ae7-a93a-7081f6af377d

-- Sol generated from Tropical/KneeMedian/MedianEquivariance.lean
import Mathlib
import Definitions.Def_Tropical_KneeMedian_MedianEquivariance
/-
# Order-reversal equivariance of the median (tropical robust statistics)

This file develops, for an arbitrary linear order, the *counting* characterisation
of the median of an odd multiset

    `IsMedian k s m  ↔  m ∈ s ∧ #{x ∈ s | x ≤ m} ≥ k+1 ∧ #{x ∈ s | m ≤ x} ≥ k+1`

for `card s = 2k+1`, and proves the three structural theorems that make the
median the *canonical centre* of a seed distribution:

* `IsMedian.unique` — the median is unique (a counting/pigeonhole argument);
* `exists_isMedian` — the median exists (via the sorted representative);
* `IsMedian.map_mono` / `IsMedian.map_anti` — the median is equivariant under
  order-preserving **and** order-reversing reparametrisations of the sample.

The last pair is the structural content behind the empirical "7/8-median law"
of the NET-48 attention-cost thread: normalising knees by the product point
`P = d·ctx/32` is an order-preserving reparametrisation, while converting a
knee `k*` into a deployment speed-up `ctx / k*` is an order-*reversing* one.
Both leave the median where it is, so the median knee, the median ratio and the
median speed-up are the same statistic read in three coordinate systems.  The
extremes (min / max) do **not** have this property: order reversal swaps them
(`isLeast_map_of_isGreatest`), which is exactly why the "guaranteed"
speed-up is governed by the *largest* knee while the "median" speed-up is
governed by the median knee.
-/

open Catalog.Tropical.KneeMedian

open Multiset

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-! ## The counting characterisation of a median -/




/-! ## Existence via the sorted representative -/




/-! ## Equivariance -/




/-! ## The extremes are *not* order-reversal equivariant -/



open Catalog.Tropical.KneeMedian in
omit [LinearOrder α] in
theorem solution(p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, ¬(p x ∧ q x)) (s : Multiset α) :
    card (s.filter p) + card (s.filter q) ≤ card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have hna := hpq a
      by_cases hp : p a
      · have hq : ¬ q a := fun h => hna ⟨hp, h⟩
        rw [Multiset.filter_cons_of_pos _ hp, Multiset.filter_cons_of_neg _ hq]
        simp only [Multiset.card_cons]
        omega
      · rw [Multiset.filter_cons_of_neg _ hp]
        by_cases hq : q a
        · rw [Multiset.filter_cons_of_pos _ hq]
          simp only [Multiset.card_cons]
          omega
        · rw [Multiset.filter_cons_of_neg _ hq]
          simp only [Multiset.card_cons]
          omega
