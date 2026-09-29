-- Prove2me | solution 1 for ScanSchemeDecoding.triangle_tangent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:51:57.225286+00:00
-- url     : https://prove2.me/submissions/4136e0c6-aaf7-4cc1-a568-9b4ad91232e9

-- Sol generated from Algebra/ScanSchemeDecoding/Triangle.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_two_mul_triangle

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
theorem solution(q k : ℕ) :
    (triangle q : ℤ) + ((q : ℤ) + 1) * ((k : ℤ) - q) ≤ (triangle k : ℤ) := by
  have hd : 0 ≤ ((k : ℤ) - q) * ((k : ℤ) - q - 1) := by
    rcases le_or_gt (k : ℤ) q with h | h
    · have h1 : (k : ℤ) - q ≤ 0 := by linarith
      have h2 : (k : ℤ) - q - 1 ≤ 0 := by linarith
      nlinarith
    · have h1 : (1 : ℤ) ≤ (k : ℤ) - q := by omega
      nlinarith
  have hq : (2 : ℤ) * triangle q = (q : ℤ) * (q + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (two_mul_triangle q)
  have hk : (2 : ℤ) * triangle k = (k : ℤ) * (k + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (two_mul_triangle k)
  nlinarith
