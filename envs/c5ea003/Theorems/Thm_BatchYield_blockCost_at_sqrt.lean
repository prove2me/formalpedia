-- Prove2me | Theorems.Thm_BatchYield_blockCost_at_sqrt
-- name    : BatchYield.blockCost_at_sqrt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:12.744826+00:00
-- url     : https://prove2.me/theorems/4a8c5401-7817-4bd4-ac34-462b583e08d2
-- title:
--   The bound is attained at `k* = √(A/q)`.
-- statement:
--   The bound is attained at `k* = √(A/q)`.
--
--   ```lean
--   theorem BatchYield.blockCost_at_sqrt{A c q : ℝ} (hA : 0 < A) (hq : 0 < q) :
--       blockCost A c q (Real.sqrt (A / q)) = c - q + 2 * Real.sqrt (A * q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BatchSmoothnessYield.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BatchSmoothnessYield.lean#L170

-- Thm stub generated from Applications/BatchSmoothnessYield.lean
import Mathlib
import Definitions.Def_Applications_BatchSmoothnessCorrectness
import Definitions.Def_Applications_BatchSmoothnessYield

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

theorem BatchYield.blockCost_at_sqrt{A c q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    blockCost A c q (Real.sqrt (A / q)) = c - q + 2 * Real.sqrt (A * q) := by sorry
