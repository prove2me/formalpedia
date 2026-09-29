-- Prove2me | Theorems.Thm_FactoringBarriers_geom_mean_le_arith_mean_of_card
-- name    : FactoringBarriers.geom_mean_le_arith_mean_of_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:50:09.815497+00:00
-- url     : https://prove2.me/theorems/2f29c169-7cc8-40ba-88b9-7daa6f37e29a
-- title:
--   Arithmetic–geometric mean inequality in the balanced-weight form: the
-- statement:
--   Arithmetic–geometric mean inequality in the balanced-weight form: the
--   geometric mean of `k` positive reals is at most their arithmetic mean.
--
--   ```lean
--   theorem FactoringBarriers.geom_mean_le_arith_mean_of_card{k : ℕ} (hk : 0 < k) (y : Fin k → ℝ)
--       (hy : ∀ i, 0 ≤ y i) :
--       (∏ i, y i) ^ (1 / (k : ℝ)) ≤ (∑ i, y i) / k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FactoringBarriers/TradeoffBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FactoringBarriers/TradeoffBarrier.lean#L40

-- Thm stub generated from Cryptography/FactoringBarriers/TradeoffBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder

/-!
# Why the Exponents Are `1/2` and `1/3`: The Multiplicative Trade-off Barrier

The subexponential factoring algorithms all have running times of the shape
`L[1/k, c]`, with `k = 2` for CFRAC / quadratic sieve / ECM and `k = 3` for the
number field sieve.  This file isolates the *structural* reason, as a theorem
about the shape of the cost function rather than a fact about any particular
algorithm.

**Model.** A `k`-way trade-off strategy splits the work into `k` exponential
stages of costs `exp (y 0), …, exp (y (k-1))`, where the "budget" parameters
`y i` are subject to a *multiplicative* constraint `∏ i, y i = x`
(`x = log N`): making one stage cheaper makes another proportionally more
expensive.  Sieving is the canonical example: the smoothness bound and the
relation-collection effort trade off multiplicatively in `log N`.

**Main results.**

* `tradeoff_lower_bound` — every `k`-way trade-off costs at least
  `k · exp (x^{1/k})`; the exponent `1/k` is forced by AM–GM, not chosen.
* `tradeoff_attained` — the bound is exactly attained at the balanced point
  `y i = x^{1/k}`, so it is sharp and the model is not an over-estimate.
* `tradeoff_cost_superpoly` — for each *fixed* `k`, `k · exp (x^{1/k})` is
  superpolynomial: no fixed-arity trade-off strategy can run in polynomial time.
* `tradeoff_unbounded_arity_is_poly` — and here is the honest boundary: if the
  arity `k` may grow with the input, the same expression drops to
  `O(log N)`.  A `k`-way trade-off barrier is therefore a statement about
  *bounded* arity; escaping it requires unboundedly many balanced stages,
  which is precisely the structural novelty no classical method supplies.
-/

open FactoringBarriers

open Filter Finset Real
open scoped Topology

/-! ## AM–GM in the two forms we need -/

theorem FactoringBarriers.geom_mean_le_arith_mean_of_card{k : ℕ} (hk : 0 < k) (y : Fin k → ℝ)
    (hy : ∀ i, 0 ≤ y i) :
    (∏ i, y i) ^ (1 / (k : ℝ)) ≤ (∑ i, y i) / k := by sorry
