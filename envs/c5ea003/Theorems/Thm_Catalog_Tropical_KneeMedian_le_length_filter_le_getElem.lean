-- Prove2me | Theorems.Thm_Catalog_Tropical_KneeMedian_le_length_filter_le_getElem
-- name    : Catalog.Tropical.KneeMedian.le_length_filter_le_getElem
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:34:20.923696+00:00
-- url     : https://prove2.me/theorems/58e2c5d9-6c20-4f14-9310-6d56e4703027
-- title:
--   In a sorted list, the first `i+1` entries are all `≤ l[i]`, hence at least `i+1`
-- statement:
--   In a sorted list, the first `i+1` entries are all `≤ l[i]`, hence at least `i+1`
--   entries pass the test `· ≤ l[i]`.
--
--   ```lean
--   theorem Catalog.Tropical.KneeMedian.le_length_filter_le_getElem{l : List α} (hl : l.Pairwise (· ≤ ·)) {i : ℕ}
--       (hi : i < l.length) :
--       i + 1 ≤ (l.filter (fun x => decide (x ≤ l[i]))).length := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/KneeMedian/MedianEquivariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/KneeMedian/MedianEquivariance.lean#L88

-- Thm stub generated from Tropical/KneeMedian/MedianEquivariance.lean
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

theorem Catalog.Tropical.KneeMedian.le_length_filter_le_getElem{l : List α} (hl : l.Pairwise (· ≤ ·)) {i : ℕ}
    (hi : i < l.length) :
    i + 1 ≤ (l.filter (fun x => decide (x ≤ l[i]))).length := by sorry
