-- Prove2me | solution 1 for Catalog.Tropical.KneeMedian.le_length_filter_le_getElem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:44:14.31157+00:00
-- url     : https://prove2.me/submissions/fe9efc49-3ed3-4c9d-b9c5-b4d296d97970

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
theorem solution{l : List α} (hl : l.Pairwise (· ≤ ·)) {i : ℕ}
    (hi : i < l.length) :
    i + 1 ≤ (l.filter (fun x => decide (x ≤ l[i]))).length := by
  have hsub : (l.take (i + 1)).Sublist l := List.take_sublist _ _
  have hall : ∀ x ∈ l.take (i + 1), decide (x ≤ l[i]) = true := by
    intro x hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    rw [List.getElem_take] at hjx
    have hjlen : j < i + 1 := by
      rw [List.length_take] at hj; omega
    have hle : l[j] ≤ l[i] := by
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hjlen) with h | h
      · simp [h]
      · exact (List.pairwise_iff_getElem.mp hl) j i (by omega) hi h
    simp [← hjx, hle]
  have hfil : (l.take (i + 1)).filter (fun x => decide (x ≤ l[i])) = l.take (i + 1) :=
    List.filter_eq_self.mpr hall
  have hsl := hsub.filter (fun x => decide (x ≤ l[i]))
  have hlen : (l.take (i + 1)).length = i + 1 := by
    rw [List.length_take]; omega
  calc i + 1 = ((l.take (i + 1)).filter (fun x => decide (x ≤ l[i]))).length := by
        rw [hfil, hlen]
    _ ≤ _ := hsl.length_le
