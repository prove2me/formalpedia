-- Prove2me | Theorems.Thm_Catalog_Tropical_KneeMedian_IsMedian_unique
-- name    : Catalog.Tropical.KneeMedian.IsMedian.unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:33:55.77759+00:00
-- url     : https://prove2.me/theorems/617dcede-aa57-44e2-adaa-69903f5b904f
-- title:
--   Uniqueness of the median.
-- statement:
--   **Uniqueness of the median.**  A pigeonhole argument: if `m < m'` were two medians,
--   the `k+1` entries `≤ m` and the `k+1` entries `≥ m'` would be disjoint, forcing
--   `2k+2 ≤ 2k+1`.
--
--   ```lean
--   theorem Catalog.Tropical.KneeMedian.IsMedian.unique{k : ℕ} {s : Multiset α} {m m' : α} (hcard : card s = 2 * k + 1)
--       (h : IsMedian k s m) (h' : IsMedian k s m') : m = m' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/KneeMedian/MedianEquivariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/KneeMedian/MedianEquivariance.lean#L68

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

theorem Catalog.Tropical.KneeMedian.IsMedian.unique{k : ℕ} {s : Multiset α} {m m' : α} (hcard : card s = 2 * k + 1)
    (h : IsMedian k s m) (h' : IsMedian k s m') : m = m' := by sorry
