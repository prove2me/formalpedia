-- Prove2me | solution 1 for ScanSchemeDecoding.sum_tangent_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:51:56.616073+00:00
-- url     : https://prove2.me/submissions/5a5739aa-d6a4-473c-8803-df32fb906d6e

-- Sol generated from Algebra/ScanSchemeDecoding/Triangle.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_triangleOpt_eq

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
theorem solution{m : ℕ} (hm : 0 < m) (f : Fin m → ℕ) (N : ℕ) (hf : ∑ i, f i = N) :
    ∑ i : Fin m, ((triangle (N / m) : ℤ)
        + (((N / m : ℕ) : ℤ) + 1) * ((f i : ℤ) - ((N / m : ℕ) : ℤ)))
      = (triangleOpt N m : ℤ) := by
  have hN : m * (N / m) + N % m = N := Nat.div_add_mod N m
  have hfz : ∑ i : Fin m, (f i : ℤ) = (N : ℤ) := by rw [← Nat.cast_sum, hf]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hfz]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsub : (N : ℤ) - (m : ℤ) * ((N / m : ℕ) : ℤ) = ((N % m : ℕ) : ℤ) := by
    have hcast : ((m * (N / m) + N % m : ℕ) : ℤ) = (N : ℤ) := by exact_mod_cast hN
    push_cast at hcast ⊢
    linarith
  rw [hsub, triangleOpt_eq hm]
  push_cast
  ring
