-- Prove2me | solution 1 for BatchYield.blockCost_eq_opt_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:45:47.704293+00:00
-- url     : https://prove2.me/submissions/350990a9-16f3-4f6e-bb82-3a44e3baadbe

-- Sol generated from Applications/BatchSmoothnessYield.lean
import Mathlib
import Definitions.Def_Applications_BatchSmoothnessCorrectness
import Definitions.Def_Applications_BatchSmoothnessYield
import Theorems.Thm_BatchYield_blockCost_at_sqrt

/-!
# Optimal batch size, and the relation quota that batching feeds

Second research cycle on exp 561.  The first cycle established that the
product-tree criterion is *exact*
(`Catalog/Applications/BatchSmoothnessCorrectness.lean`) and that its cost
profile has two opposite regimes
(`Catalog/Applications/BatchSmoothnessCost.lean`): unbounded amortization in the
flat op model, quadratic blow-up in the word model.  Two questions were left
open, and both are answered here.

**Q1 (unification).**  Is the flat/word split really two phenomena, or one?
`blockCost_ge_opt` shows it is one: for a stream of candidates cut into blocks
of size `k`, the per-candidate cost is `A/k + c + q(k-1)`, where `A` is the
per-batch setup, `c` the per-candidate cost and `q` the *quadratic* big-integer
coefficient.  For `q = 0` (flat model) this is strictly decreasing — batch keeps
winning, exactly as measured up to `k = 512`.  For `q > 0` (word model) it has a
unique interior minimum at `k* = √(A/q)`, with optimal value
`c - q + 2√(Aq)` (`blockCost_eq_opt_iff`).  The measured crossover `M* ≈ 1715`
is a shadow of this square root, not of the tree depth.

**Q2 (what the smooth pool is for).**  Exp 561 reports `qs_splits_total = 0` at
bit length 40 / factor base 100: yield below quota.  `exists_square_subproduct`
makes the quota exact — as soon as the batch produces more `B`-smooth relations
than there are primes `≤ B`, a nonempty sub-product is automatically a perfect
square.  The proof is a pigeonhole over `𝔽₂`-exponent vectors
(`exists_nonempty_subset_sum_eq_zero`), bridging linear algebra over `ZMod 2`
with the multiplicative structure of `ℕ`.

## Main results

* `exists_nonempty_subset_sum_eq_zero` — over `ZMod 2`, more vectors than
  coordinates forces a nonempty subset summing to zero (subset-pigeonhole; no
  distinctness hypothesis, so repeated relations are allowed).
* `isSquare_of_even_factorization` — even exponents everywhere means square.
* `exists_square_subproduct` — **relation quota**: `π(B) + 1` smooth relations
  always contain a nonempty sub-family whose product is a perfect square.
* `blockCost_ge_opt`, `blockCost_eq_opt_iff` — the optimal batch size is
  `√(A/q)`, sharp.
* `blockCost_strictAnti_of_flat` — with `q = 0` there is no optimum: the flat
  model's monotone win, recovered as the degenerate case.
-/

open BatchYield

open Finset BatchSmoothness

/-! ## Pigeonhole over `𝔽₂` -/


/-! ## Even exponents give squares -/


/-! ## The relation quota of the sieve -/



/-! ## Optimal batch size: one formula for both regimes -/








open BatchYield in
theorem solution{A c q k : ℝ} (hA : 0 < A) (hq : 0 < q) (hk : 0 < k) :
    blockCost A c q k = c - q + 2 * Real.sqrt (A * q) ↔ k = Real.sqrt (A / q) := by
  constructor
  · intro h
    unfold blockCost at h
    have h1 : Real.sqrt (A / k) ^ 2 = A / k := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (q * k) ^ 2 = q * k := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt (A / k) * Real.sqrt (q * k) = Real.sqrt (A * q) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    have hzero : (Real.sqrt (A / k) - Real.sqrt (q * k)) ^ 2 = 0 := by nlinarith
    have heq : Real.sqrt (A / k) = Real.sqrt (q * k) := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
      linarith
    have hk2 : A / k = q * k := by rw [← h1, ← h2, heq]
    have hkk : k ^ 2 = A / q := by
      rw [eq_div_iff hq.ne']
      field_simp at hk2
      nlinarith [hk2]
    rw [← hkk, Real.sqrt_sq hk.le]
  · intro h; rw [h]; exact blockCost_at_sqrt hA hq
