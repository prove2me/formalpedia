-- Prove2me | Theorems.Thm_ScanSchemeDecoding_two_mul_triangle
-- name    : ScanSchemeDecoding.two_mul_triangle
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:56:32.284365+00:00
-- url     : https://prove2.me/theorems/b7e8ed3a-7d5a-4d9c-9312-914a28b3c425
-- title:
--   Two mul triangle
-- statement:
--   Formal statement of `ScanSchemeDecoding.two_mul_triangle` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ScanSchemeDecoding.two_mul_triangle(k : ℕ) : 2 * triangle k = k * (k + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Triangle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Triangle.lean#L40

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

theorem ScanSchemeDecoding.two_mul_triangle(k : ℕ) : 2 * triangle k = k * (k + 1) := by sorry
