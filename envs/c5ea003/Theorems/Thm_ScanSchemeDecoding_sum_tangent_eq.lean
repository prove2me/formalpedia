-- Prove2me | Theorems.Thm_ScanSchemeDecoding_sum_tangent_eq
-- name    : ScanSchemeDecoding.sum_tangent_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:56:54.633636+00:00
-- url     : https://prove2.me/theorems/c887b579-07c8-4f72-890a-cd47260edb92
-- title:
--   The tangent lower bounds sum exactly to the optimum: the tangent line at the
-- statement:
--   The tangent lower bounds sum **exactly** to the optimum: the tangent line at the
--   balanced size is tight on average, which is what makes the bound below sharp.
--
--   ```lean
--   theorem ScanSchemeDecoding.sum_tangent_eq{m : ℕ} (hm : 0 < m) (f : Fin m → ℕ) (N : ℕ) (hf : ∑ i, f i = N) :
--       ∑ i : Fin m, ((triangle (N / m) : ℤ)
--           + (((N / m : ℕ) : ℤ) + 1) * ((f i : ℤ) - ((N / m : ℕ) : ℤ)))
--         = (triangleOpt N m : ℤ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Triangle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Triangle.lean#L90

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

theorem ScanSchemeDecoding.sum_tangent_eq{m : ℕ} (hm : 0 < m) (f : Fin m → ℕ) (N : ℕ) (hf : ∑ i, f i = N) :
    ∑ i : Fin m, ((triangle (N / m) : ℤ)
        + (((N / m : ℕ) : ℤ) + 1) * ((f i : ℤ) - ((N / m : ℕ) : ℤ)))
      = (triangleOpt N m : ℤ) := by sorry
