-- Prove2me | solution 1 for Catalog.Tropical.KneeMedian.exists_isMedian
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:47:23.900947+00:00
-- url     : https://prove2.me/submissions/d49df80c-d2cf-440e-9db1-e999943e5c3b

-- Sol generated from Tropical/KneeMedian/MedianEquivariance.lean
import Mathlib
import Definitions.Def_Tropical_KneeMedian_MedianEquivariance
import Theorems.Thm_Catalog_Tropical_KneeMedian_le_length_filter_getElem_le
import Theorems.Thm_Catalog_Tropical_KneeMedian_le_length_filter_le_getElem
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
theorem solution{k : ℕ} {s : Multiset α} (hcard : card s = 2 * k + 1) :
    ∃ m, IsMedian k s m := by
  classical
  set l : List α := s.sort (· ≤ ·) with hl
  have hs : s = (l : Multiset α) := (Multiset.sort_eq s _).symm
  have hlen : l.length = 2 * k + 1 := by rw [hl, Multiset.length_sort, hcard]
  have hsorted : l.Pairwise (· ≤ ·) := Multiset.pairwise_sort s _
  have hk : k < l.length := by omega
  refine ⟨l[k], ?_, ?_, ?_⟩
  · rw [hs]; exact Multiset.mem_coe.mpr (List.getElem_mem hk)
  · have h := le_length_filter_le_getElem hsorted hk
    rw [hs]
    simpa [Multiset.filter_coe] using h
  · have h := le_length_filter_getElem_le hsorted hk
    rw [hs]
    simp only [Multiset.filter_coe, Multiset.coe_card]
    omega
