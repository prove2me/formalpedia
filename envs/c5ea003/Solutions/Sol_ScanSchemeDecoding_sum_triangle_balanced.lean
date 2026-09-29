-- Prove2me | solution 1 for ScanSchemeDecoding.sum_triangle_balanced
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:08:33.760025+00:00
-- url     : https://prove2.me/submissions/03bba462-d605-4c7e-8d28-f2abe09c5c7c

-- Sol generated from Algebra/ScanSchemeDecoding/Triangle.lean
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













lemma card_filter_lt (m r : ℕ) (hr : r ≤ m) :
    (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r)).card = r := by
  classical
  have : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r))
      = (Finset.range r).attachFin (fun j hj => lt_of_lt_of_le (Finset.mem_range.mp hj) hr) := by
    ext i
    simp [Finset.mem_attachFin]
  rw [this]
  simp

lemma sum_ite_lt {M : Type*} [AddCommMonoid M] (m r : ℕ) (hr : r ≤ m) (a b : M) :
    ∑ i : Fin m, (if (i : ℕ) < r then a else b) = r • a + (m - r) • b := by
  classical
  rw [Finset.sum_ite]
  have h1 : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r)).card = r :=
    card_filter_lt m r hr
  have h2 : (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < r)).card = m - r := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m))) (p := fun i : Fin m => (i : ℕ) < r)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [Finset.sum_const, Finset.sum_const, h1, h2]





open ScanSchemeDecoding in
theorem solution{m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ i, triangle (balancedProfile N m i) = triangleOpt N m := by
  have hr : N % m < m := Nat.mod_lt _ hm
  unfold balancedProfile triangleOpt
  have : ∀ i : Fin m, triangle (N / m + (if (i : ℕ) < N % m then 1 else 0))
      = if (i : ℕ) < N % m then triangle (N / m + 1) else triangle (N / m) := by
    intro i; by_cases h : (i : ℕ) < N % m <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => this i),
    sum_ite_lt m (N % m) hr.le (triangle (N / m + 1)) (triangle (N / m))]
  simp [smul_eq_mul]
