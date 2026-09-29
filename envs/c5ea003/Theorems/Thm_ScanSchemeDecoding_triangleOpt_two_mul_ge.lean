-- Prove2me | Theorems.Thm_ScanSchemeDecoding_triangleOpt_two_mul_ge
-- name    : ScanSchemeDecoding.triangleOpt_two_mul_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:58:48.373755+00:00
-- url     : https://prove2.me/theorems/15592f7f-0870-4520-9059-5afd0152916b
-- title:
--   Averaged (`ε`-)form of the optimum.
-- statement:
--   **Averaged (`ε`-)form of the optimum.**  With `m = ⌊εN⌋` buckets the mean decoding
--   cost is at least `(N / m + 1) / 2`: no bucketing scheme can do better than half the
--   average bucket size.
--
--   ```lean
--   theorem ScanSchemeDecoding.triangleOpt_two_mul_ge{m : ℕ} (hm : 0 < m) (N : ℕ) :
--       N * (N / m + 1) ≤ 2 * triangleOpt N m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Triangle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Triangle.lean#L168

-- Thm stub generated from Algebra/ScanSchemeDecoding/Triangle.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle

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

theorem ScanSchemeDecoding.triangleOpt_two_mul_ge{m : ℕ} (hm : 0 < m) (N : ℕ) :
    N * (N / m + 1) ≤ 2 * triangleOpt N m := by sorry
