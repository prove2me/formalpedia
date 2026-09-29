-- Prove2me | Definitions.Def_Tropical_KneeMedian_MedianEquivariance
-- name    : Tropical_KneeMedian_MedianEquivariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:01.087944+00:00
-- url     : https://prove2.me/theorems/812cbb0b-b1e8-4aca-b8a6-d93875391b6f
-- title:
--   Aether Catalog definitions — Tropical_KneeMedian_MedianEquivariance
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.KneeMedian.MedianEquivariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/KneeMedian/MedianEquivariance.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Tropical.KneeMedian

open Multiset

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-! ## The counting characterisation of a median -/

/-- `IsMedian k s m` says that `m` is a median of a multiset `s` of odd size `2k+1`:
`m` occurs in `s`, at least `k+1` entries are `≤ m` and at least `k+1` entries are `≥ m`. -/
structure IsMedian (k : ℕ) (s : Multiset α) (m : α) : Prop where
  mem : m ∈ s
  lower : k + 1 ≤ card (s.filter (fun x => x ≤ m))
  upper : k + 1 ≤ card (s.filter (fun x => m ≤ x))



/-! ## Existence via the sorted representative -/




/-! ## Equivariance -/




/-! ## The extremes are *not* order-reversal equivariant -/


end Catalog.Tropical.KneeMedian


