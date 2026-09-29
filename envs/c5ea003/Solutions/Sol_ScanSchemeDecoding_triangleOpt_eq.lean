-- Prove2me | solution 1 for ScanSchemeDecoding.triangleOpt_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:50:22.877591+00:00
-- url     : https://prove2.me/submissions/aa0b6543-450f-4702-aec7-de333fbba026

-- Sol generated from Algebra/ScanSchemeDecoding/Triangle.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_triangle_succ

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
theorem solution{m : ℕ} (hm : 0 < m) (N : ℕ) :
    triangleOpt N m = m * triangle (N / m) + N % m * (N / m + 1) := by
  have hr : N % m ≤ m := (Nat.mod_lt _ hm).le
  obtain ⟨s, hs⟩ : ∃ s, m = s + N % m := ⟨m - N % m, by omega⟩
  have hms : m - N % m = s := by omega
  have key : N % m * (triangle (N / m) + (N / m + 1)) + s * triangle (N / m)
      = (s + N % m) * triangle (N / m) + N % m * (N / m + 1) := by ring
  unfold triangleOpt
  rw [triangle_succ, hms, key, ← hs]
