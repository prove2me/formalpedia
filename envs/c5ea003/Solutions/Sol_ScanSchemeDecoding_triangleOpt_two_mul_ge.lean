-- Prove2me | solution 1 for ScanSchemeDecoding.triangleOpt_two_mul_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:10:49.829695+00:00
-- url     : https://prove2.me/submissions/e2694a9f-b537-4fc2-a881-cc8023488adc

-- Sol generated from Algebra/ScanSchemeDecoding/Triangle.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_triangle_succ
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
theorem solution{m : ℕ} (hm : 0 < m) (N : ℕ) :
    N * (N / m + 1) ≤ 2 * triangleOpt N m := by
  set q := N / m with hq
  set r := N % m with hrdef
  have hN : m * q + r = N := Nat.div_add_mod N m
  have hr : r < m := Nat.mod_lt _ hm
  obtain ⟨s, hs⟩ : ∃ s, m = s + r := ⟨m - r, by omega⟩
  have hmr : m - r = s := by omega
  unfold triangleOpt
  rw [triangle_succ, ← hq, ← hrdef, hmr]
  have h1 := two_mul_triangle q
  have hNsub : N = (s + r) * q + r := by rw [← hN, hs]
  calc N * (q + 1) = ((s + r) * q + r) * (q + 1) := by rw [← hNsub]
    _ ≤ (r + s) * (q * (q + 1)) + 2 * r * (q + 1) := by nlinarith [Nat.zero_le (r * (q+1))]
    _ = 2 * (r * (triangle q + (q + 1)) + s * triangle q) := by rw [← h1]; ring
