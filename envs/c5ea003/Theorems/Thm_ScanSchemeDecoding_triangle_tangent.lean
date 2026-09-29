-- Prove2me | Theorems.Thm_ScanSchemeDecoding_triangle_tangent
-- name    : ScanSchemeDecoding.triangle_tangent
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:57:01.416466+00:00
-- url     : https://prove2.me/theorems/f1f2638d-d8bd-4144-b4eb-3c753b4aa7ec
-- title:
--   Integral tangent-line inequality.
-- statement:
--   **Integral tangent-line inequality.**  Discrete convexity of `triangle` at the
--   point `q`, using the *upper* slope `q + 1`.  The inequality holds for every pair of
--   naturals because `(k - q) * (k - q - 1) ≥ 0` for every integer `k - q`.
--
--   ```lean
--   theorem ScanSchemeDecoding.triangle_tangent(q k : ℕ) :
--       (triangle q : ℤ) + ((q : ℤ) + 1) * ((k : ℤ) - q) ≤ (triangle k : ℤ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Triangle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Triangle.lean#L56

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

theorem ScanSchemeDecoding.triangle_tangent(q k : ℕ) :
    (triangle q : ℤ) + ((q : ℤ) + 1) * ((k : ℤ) - q) ≤ (triangle k : ℤ) := by sorry
