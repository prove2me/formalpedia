-- Prove2me | Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
-- name    : Algebra_ScanSchemeDecoding_Triangle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T09:48:25.729972+00:00
-- url     : https://prove2.me/theorems/5c52f77c-006f-4269-b49c-d3c340eaaf72
-- title:
--   Aether Catalog definitions — Algebra_ScanSchemeDecoding_Triangle
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ScanSchemeDecoding.Triangle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ScanSchemeDecoding/Triangle.lean by skeleton subtraction
import Mathlib

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

namespace ScanSchemeDecoding

open Finset

/-- `triangle k = 1 + 2 + ⋯ + k`, the cost of scanning a bucket of size `k`
when every key of the bucket is decoded once. -/
def triangle (k : ℕ) : ℕ := k * (k + 1) / 2







/-- The optimal total scan cost of `N` keys in `m` buckets. -/
def triangleOpt (N m : ℕ) : ℕ :=
  N % m * triangle (N / m + 1) + (m - N % m) * triangle (N / m)




/-- The balanced profile: `r` buckets of size `q + 1` and `m - r` of size `q`. -/
def balancedProfile (N m : ℕ) (i : Fin m) : ℕ :=
  N / m + (if (i : ℕ) < N % m then 1 else 0)






end ScanSchemeDecoding


