-- Prove2me | solution 1 for ScanSchemeDecoding.sum_triangle_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:03:42.032428+00:00
-- url     : https://prove2.me/submissions/0a2e5db3-52db-488e-a7de-42aac4b00c44

-- Sol generated from Algebra/ScanSchemeDecoding/Triangle.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_sum_tangent_eq
import Theorems.Thm_ScanSchemeDecoding_triangle_tangent

/-!
# Triangular cost and the exact `ε`-pigeonhole optimum

This file develops the arithmetic backbone of the *scan-scheme* cost model.

A scan scheme distributes `N` keys into `m` buckets; decoding a key costs its
`1`-based position inside its bucket, so a bucket holding `k` keys contributes
`1 + 2 + ⋯ + k = triangle k` to the total decoding cost.  Optimising a scheme is
therefore exactly the discrete problem

  minimise `∑ i, triangle (f i)`  subject to `f : Fin m → ℕ`, `∑ i, f i = N`.

## Main results

* `ScanSchemeDecoding.triangle_tangent` — the *integral tangent-line inequality*
  `triangle q + (q+1) * (k - q) ≤ triangle k`, valid for **all** naturals `k, q`
  (over `ℤ`), the discrete convexity fact driving everything below.
* `ScanSchemeDecoding.sum_triangle_ge` — the exact pigeonhole lower bound
  `r * triangle (q+1) + (m - r) * triangle q ≤ ∑ i, triangle (f i)` where
  `q = N / m`, `r = N % m`.
* `ScanSchemeDecoding.sum_triangle_balanced` — the balanced profile attains it,
  so the bound is the *exact* optimum, not merely a bound.
* `ScanSchemeDecoding.triangleOpt_two_mul_ge` — the averaged ("`ε`") form:
  `N * (N / m + 1) ≤ 2 * optimum`.
-/

open ScanSchemeDecoding

open Finset



















open ScanSchemeDecoding in
theorem solution{m : ℕ} (hm : 0 < m) (f : Fin m → ℕ) (N : ℕ)
    (hf : ∑ i, f i = N) : triangleOpt N m ≤ ∑ i, triangle (f i) := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    triangle_tangent (N / m) (f i))
  rw [sum_tangent_eq hm f N hf] at hsum
  have hcast : (triangleOpt N m : ℤ) ≤ ((∑ i, triangle (f i) : ℕ) : ℤ) := by
    rw [Nat.cast_sum]; exact hsum
  exact_mod_cast hcast
