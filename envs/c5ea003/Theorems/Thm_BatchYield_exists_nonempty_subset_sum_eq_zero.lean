-- Prove2me | Theorems.Thm_BatchYield_exists_nonempty_subset_sum_eq_zero
-- name    : BatchYield.exists_nonempty_subset_sum_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:31.841633+00:00
-- url     : https://prove2.me/theorems/2d75e624-7fa6-4011-b398-e1c90c2a0a8f
-- title:
--   Subset pigeonhole over `ZMod 2`.
-- statement:
--   **Subset pigeonhole over `ZMod 2`.**  If there are strictly more vectors
--   than coordinates then some nonempty subset of them sums to zero.  Unlike the
--   usual linear-dependence statement, the family need not be injective: repeated
--   relations are allowed, which is what a smoothness batch actually produces.
--
--   ```lean
--   theorem BatchYield.exists_nonempty_subset_sum_eq_zero{ι κ : Type*} [Fintype ι] [DecidableEq ι]
--       [Fintype κ] [DecidableEq κ] (v : ι → (κ → ZMod 2))
--       (h : Fintype.card κ < Fintype.card ι) :
--       ∃ S : Finset ι, S.Nonempty ∧ ∑ i ∈ S, v i = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BatchSmoothnessYield.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BatchSmoothnessYield.lean#L51

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

theorem BatchYield.exists_nonempty_subset_sum_eq_zero{ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (v : ι → (κ → ZMod 2))
    (h : Fintype.card κ < Fintype.card ι) :
    ∃ S : Finset ι, S.Nonempty ∧ ∑ i ∈ S, v i = 0 := by sorry
